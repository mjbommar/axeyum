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
    /// `CPoint.Scalar.one_sub_inv2 : Equiv (add CReal.one (neg inv2)) inv2`
    /// — `1 - 1/2 = 1/2`. Isolated because [`Self::stewart`]'s `t := inv2`
    /// specialisation carries a `mul (add one (neg t)) …` factor that must be
    /// rewritten to `mul inv2 …` before it reads as a median-length relation
    /// ([`Self::stewart_median`]).
    pub one_sub_inv2: NameId,
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
    /// **The orthocentre identity, unconditional.** `∀ P A B C,
    /// Equiv (add (add (dot (sub P A) (sub C B)) (dot (sub P B) (sub A C)))
    ///            (dot (sub P C) (sub B A)))
    ///       zero`.
    ///
    /// Pure bilinearity: writing `u := A-P, v := B-P, w := C-P`, each summand
    /// telescopes (`P-A ~ neg u`, `C-B ~ w-v`, …, via
    /// `diff_diff_scalar_proof` and `neg_sub_comm_scalar_proof`) into a
    /// difference of two raw dot products, and the three differences form a
    /// 3-cycle `(u·v - v·u) + (v·w - w·v) + (w·u - u·w)` that cancels term by
    /// term via [`Self::dot_comm`]. No hypothesis, for every configuration —
    /// this is what makes [`Self::orthocentre_third_altitude`] (two altitudes
    /// meeting forces the third through the same point) unconditional too.
    pub orthocentre_identity: NameId,
    /// **Concurrence of the altitudes.** `∀ P A B C,
    /// Equiv (dot (sub P A) (sub C B)) zero →
    /// Equiv (dot (sub P B) (sub A C)) zero →
    /// Equiv (dot (sub P C) (sub B A)) zero`.
    ///
    /// `(P-A)·(C-B) ~ 0` says `PA ⊥ BC`, the altitude from `A`; similarly for
    /// `B`. The conclusion is the altitude from `C` through the same point
    /// `P`. Immediate from [`Self::orthocentre_identity`]: the two hypotheses
    /// make the first two summands of that 3-term sum vanish, so the third
    /// must too.
    pub orthocentre_third_altitude: NameId,
    /// `CPoint.distSq P Q := CPoint.dot (CPoint.sub P Q) (CPoint.sub P Q)` —
    /// squared Euclidean distance. Purely a naming device (definitionally
    /// equal to the raw `dot`/`sub` term [`Self::pythagoras`] etc. are stated
    /// over), but it is what lets [`Self::parallelogram_diagonals_bisect`]'s
    /// sibling squared-length facts read as geometry rather than algebra.
    pub dist_sq: NameId,
    /// `CPoint.distSq_congr : ∀ P P' Q Q', CPoint.Equiv P P' → CPoint.Equiv Q Q' →
    /// Equiv (distSq P Q) (distSq P' Q')`.
    pub dist_sq_congr: NameId,
    /// `CPoint.distSq_comm : ∀ P Q, Equiv (distSq P Q) (distSq Q P)`.
    pub dist_sq_comm: NameId,
    /// `CPoint.distSq_self_zero : ∀ P, Equiv (distSq P P) CReal.zero`.
    pub dist_sq_self_zero: NameId,
    /// **Elements I.47, restated over `distSq`.** `∀ A B C,
    /// Equiv (dot (sub A C) (sub B C)) zero →
    /// Equiv (distSq A B) (add (distSq A C) (distSq B C))`.
    ///
    /// A *new* declaration, not [`Self::pythagoras`] edited: its `value` is
    /// literally [`Self::pythagoras`] applied to the same three points, and
    /// the kernel accepts it against this `distSq`-headed type only because
    /// `distSq` unfolds (delta) to exactly the `dot (sub _ _) (sub _ _)` shape
    /// [`Self::pythagoras`] is already stated over — no new proof term is
    /// built, only a new (defeq) type is checked against the old value.
    pub pythagoras_dist_sq: NameId,
    /// **Parallelogram diagonals bisect each other.** `∀ A B C D,
    /// CPoint.Equiv (CPoint.sub B A) (CPoint.sub C D) →
    /// CPoint.Equiv (CPoint.midpoint A C) (CPoint.midpoint B D)`.
    ///
    /// `B − A ~ C − D` is the vector form of "`ABDC`... — concretely,
    /// `AB` and `DC` are the same displacement — is a parallelogram"; the
    /// conclusion is its two diagonals `AC`/`BD` sharing a midpoint. Pure
    /// midpoint algebra (`diag_bisect_midpoint_scalar_proof`), the same
    /// `add_assoc`/`add_comm`/`add_congr` toolkit as
    /// [`Self::varignon_diagonals_bisect`], no hypothesis beyond the
    /// parallelogram condition itself.
    pub parallelogram_diagonals_bisect: NameId,
    /// **Opposite sides of a parallelogram are equal in length.** `∀ A B C D,
    /// CPoint.Equiv (CPoint.sub B A) (CPoint.sub C D) →
    /// And (Equiv (distSq C D) (distSq A B)) (Equiv (distSq D A) (distSq B C))`.
    ///
    /// The scoped-down result actually landed for "the parallelogram law"
    /// slice: `distSq A B + distSq B C + distSq C D + distSq D A ~ distSq A C
    /// + distSq B D` (the full sum-of-squares identity, unconditional or
    /// under this same hypothesis) needs expanding two diagonals'
    /// `dot`-bilinearity in addition to this fact and was not reached in the
    /// time available — this theorem is the two "opposite sides equal" facts
    /// that identity would reduce to, each independently a real (and
    /// independently checkable) instance of the parallelogram law.
    /// `CD ~ -(AB)` follows from the hypothesis directly
    /// (`opposite_side_neg_scalar_proof`), `DA ~ -(BC)` from that plus pure
    /// ring algebra (`diag_side_neg_scalar_proof`); `dot(X,X) ~ dot(-X,-X)`
    /// ([`dot_neg_neg_proof`]) turns each into a `distSq` equality.
    pub parallelogram_opposite_sides_eq: NameId,
    /// `CPoint.dot_self_add : ∀ U V,
    /// Equiv (dot (add U V) (add U V))
    ///       (add (dot U U) (add (dot U V) (add (dot U V) (dot V V))))`.
    ///
    /// The bilinear expansion the previous lane's doc comment named as
    /// missing: `dot(u+v,u+v) ~ u² + 2uv + v²`, with `2·X` written `X+X`
    /// (this file's convention — no `CReal`-times-`Nat` scalar
    /// multiplication exists to write `2` any other way). Pure
    /// `dot_add_left`/`dot_add_right`/`dot_comm`/`add_assoc` algebra, no
    /// hypothesis, unconditional for every `U, V`.
    pub dot_self_add: NameId,
    /// `CPoint.dot_self_sub : ∀ U V,
    /// Equiv (dot (sub U V) (sub U V))
    ///       (add (dot U U) (add (neg (dot U V)) (add (neg (dot U V)) (dot V V))))`.
    ///
    /// The minus sibling of [`Self::dot_self_add`]: `dot(u-v,u-v) ~ u² - 2uv +
    /// v²`, with `-2·X` written as two separately negated `X` terms (`(-X) +
    /// (-X)`) rather than `-(X+X)` — an equally faithful instantiation of the
    /// `X+X` convention for `2X`, and the shape that falls straight out of
    /// `dot_sub_left`/`dot_sub_right` without an extra distributivity step.
    /// Pure bilinearity, no hypothesis.
    pub dot_self_sub: NameId,
    /// `CPoint.dot_self_add3 : ∀ U V W,
    /// Equiv (dot (add (add U V) W) (add (add U V) W))
    ///       (add (add (dot U U) (add (dot U V) (add (dot U V) (dot V V))))
    ///            (add (add (dot U W) (dot V W))
    ///                 (add (add (dot U W) (dot V W)) (dot W W))))`.
    ///
    /// The trinomial expansion `dot((u+v)+w,(u+v)+w) ~ (u²+2uv+v²) +
    /// (2uw+2vw+w²)` the previous lane's [`Self::parallelogram_law`] doc
    /// comment named as the missing piece for the unconditional four-point
    /// identity: [`Self::dot_self_add`] applied at `(U+V, W)`, then again at
    /// `(U, V)` to expand the inner `dot(U+V,U+V)`, then
    /// [`Self::dot_add_left`] to expand `dot(U+V,W)` (both occurrences). No
    /// hypothesis, unconditional for every `U, V, W`.
    pub dot_self_add3: NameId,
    /// **The parallelogram law: the sum of the squares of all four sides
    /// equals the sum of the squares of the two diagonals.** `∀ A B C D,
    /// CPoint.Equiv (CPoint.sub B A) (CPoint.sub C D) →
    /// Equiv (add (add (add (distSq A B) (distSq B C)) (distSq C D)) (distSq D A))
    ///       (add (distSq A C) (distSq B D))`.
    ///
    /// This is the identity [`Self::parallelogram_opposite_sides_eq`]'s doc
    /// comment named as unreached. Writing `u := sub A B`, `v := sub B C`:
    /// the hypothesis gives `sub C D ~ neg u`
    /// (`opposite_side_neg_scalar_proof`, as before) and `sub D A ~ neg v`
    /// (`diag_side_neg_scalar_proof`); the diagonals telescope
    /// *unconditionally* (no hypothesis needed for this half) to `sub A C ~
    /// add u v` and `sub B D ~ sub v u`. Expanding both diagonals' squared
    /// length via [`Self::dot_self_add`]/[`Self::dot_self_sub`] and folding
    /// `dot v u` back to `dot u v` via [`Self::dot_comm`] leaves eight terms
    /// on the diagonal side and four on the side side; `sum_of_squares_combine_proof`
    /// (pure `CReal` ring algebra in three opaque terms `a := dot u u, b :=
    /// dot u v, c := dot v v`) shows both reduce to `(a+a)+(c+c)`.
    ///
    /// **Not proved: the general, hypothesis-free four-point identity**
    /// (Euler's quadrilateral theorem), the unconditional sum `distSq A B
    /// plus distSq B C plus distSq C D plus distSq D A`, equal to `(distSq A
    /// C plus distSq B D) plus dot W W` where `W := add (sub A B) (sub C D)`
    /// — worked out on paper but not implemented in the time available.
    /// Without the hypothesis, `sub D A` telescopes to `neg (add (add u v)
    /// w)` for an *independent* third vector `w := sub C D` (not to `neg
    /// v`), which needs one more `dot_self_add` nesting
    /// (`dot((u+v)+w,(u+v)+w)`, a trinomial expansion) that this file does
    /// not build. This theorem is the hypothesis-specialised case, reached by
    /// the more direct route above rather than as a corollary of the general
    /// theorem.
    pub parallelogram_law: NameId,
    /// **Euler's quadrilateral theorem, unconditional, for every four
    /// points.** `∀ A B C D,
    /// Equiv (add (distSq A B) (add (distSq B C) (add (distSq C D) (distSq D A))))
    ///       (add (add (distSq A C) (distSq B D)) (dot W W))`,
    /// where `W := add (sub A B) (sub C D)`.
    ///
    /// No hypothesis: writing `u := sub A B`, `v := sub B C`, `w := sub C D`,
    /// the diagonals telescope unconditionally to `sub A C ~ add u v` and
    /// `sub B D ~ add v w` (`telescope_scalar_proof`, reused directly —
    /// unlike [`Self::parallelogram_law`]'s `sub B D`, this one needs no
    /// hypothesis at all), and `sub D A ~ neg (add (add u v) w)` (the same
    /// telescope plus one `neg`/`neg_sub_comm` step). Expanding `distSq D A`
    /// via [`Self::dot_self_add3`] and both diagonals via
    /// [`Self::dot_self_add`] leaves twelve terms on each side (`dot u u`,
    /// `dot v v`, `dot w w` each twice, and the three cross terms `dot u v`,
    /// `dot u w`, `dot v w` each twice); a generic right-chain
    /// flatten-and-reorder (`flatten_sum_tree`/`reorder_right_chain`, pure
    /// `add_assoc`/`add_comm`/`add_congr`, no cancellation) shows both sides
    /// are the same multiset in different association. [`Self::parallelogram_law`]
    /// is exactly this identity's specialisation at `W ~ CPoint.mk zero zero`
    /// (the hypothesis `sub B A ~ sub C D` is precisely `W ~ 0`), though this
    /// file does not derive one from the other.
    pub euler_quadrilateral: NameId,
    /// **Apollonius' median theorem.** `∀ A B C,
    /// Equiv (add (distSq A B) (distSq A C))
    ///       (add (add (distSq A M) (distSq A M)) (add (distSq B M) (distSq B M)))`,
    /// where `M := CPoint.midpoint B C` (substituted directly, not a
    /// separately quantified point — `M`'s coordinates are `midpoint (x B)(x
    /// C)`/`midpoint (y B)(y C)` by the very definition of
    /// [`Self::point_midpoint`], so no extra hypothesis is needed to pin `M`
    /// down, unlike [`Self::thales`]'s `O`).
    ///
    /// Writing `vp := sub A M` and `vq := sub B M`: `sub A B ~ sub vp vq` and
    /// `sub A C ~ add vp vq` (`diff_diff_scalar_proof` plus a `2·midpoint b
    /// c ~ b + c` bridge, `apollonius_neg_swap_scalar_proof`), so `distSq A
    /// B + distSq A C` expands via
    /// [`Self::dot_self_sub`]/[`Self::dot_self_add`] into an eight-term sum
    /// in `dot vp vp`, `dot vp vq`, `dot vq vq` (four of them negated), and
    /// the cross terms cancel (`apollonius_combine_proof`, pure `CReal` ring
    /// algebra, no `mul`) to `(dot vp vp + dot vp vp) + (dot vq vq + dot vq
    /// vq)` — `distSq A M` and `distSq B M` doubled. No hypothesis.
    pub apollonius_median: NameId,
    /// `CPoint.Scalar.three := CReal.add two one`, mirroring [`Self::two`]
    /// one level up.
    pub three: NameId,
    /// `CPoint.Scalar.threePosBound : CReal.PosBound three 0`.
    ///
    /// Admitted the same way [`Self::two_pos_bound`] is, chained one step
    /// further: `two`'s own bound gives `le one two`, and the same
    /// `le_add_of_nonneg` step `two_pos_bound` uses (anchored at `two`
    /// instead of `one`) gives `le two three`; `le_trans` composes them into
    /// `le one three`, which is `PosBound three 0` by definition.
    pub three_pos_bound: NameId,
    /// `CPoint.Scalar.inv3 := CReal.inv three 0 threePosBound` — division by
    /// three.
    pub inv3: NameId,
    /// `CPoint.Scalar.centroid a b c := CReal.mul inv3 (CReal.add a (CReal.add b c))`.
    pub centroid_scalar: NameId,
    /// `CPoint.Scalar.centroid_self : ∀ a, Equiv (centroid a a a) a`.
    ///
    /// **The discrimination witness for `centroid`**, exactly as
    /// [`Self::midpoint_self`] is for `inv2`: without this, every identity
    /// built from `centroid`/`inv3` below would hold, footprint-free, for
    /// *any* ternary scalar built the same way — it says nothing about `inv3`
    /// actually being `1/3`. This is the fact that pins it down, going
    /// through [`CRealPrelude::mul_inv_cancel`] at `three` the same way
    /// `midpoint_self` does at `two`.
    pub centroid_scalar_self: NameId,
    /// `CPoint.centroid A B C := CPoint.mk (Scalar.centroid (x A) (x B) (x C))
    /// (Scalar.centroid (y A) (y B) (y C))` — the point `(A+B+C)/3`.
    pub centroid: NameId,
    /// **The centroid divides each median, additive form.** `∀ A B C,
    /// Equiv (add (add G G) G) (add A (add M M))`, where `G := centroid A B C`
    /// and `M := point_midpoint B C`, i.e. `3G ~ A + 2M` (`2X`/`3X` spelled
    /// `X+X`/`(X+X)+X` per this file's convention).
    ///
    /// This is the additive form of "the centroid lies two-thirds of the way
    /// from each vertex to the midpoint of the opposite side": subtracting
    /// `3A` from both sides (not done here) gives the more familiar
    /// `3(G−A) ~ 2(M−A)`. Proved directly from `Self::triple_g_eq_sum_proof`
    /// (`3G ~ A+(B+C)`) and `2M ~ B+C` (`double_midpoint_proof`), no
    /// hypothesis, unconditional for every configuration.
    pub centroid_median: NameId,
    /// **The centroid divides each median 2:1, difference form.** `∀ A B C,
    /// Equiv (add (add (sub G A) (sub G A)) (sub G A)) (add (sub M A) (sub M A))`,
    /// where `G := centroid A B C`, `M := point_midpoint B C`, i.e.
    /// `3(G−A) ~ 2(M−A)` (`2X`/`3X` spelled `X+X`/`(X+X)+X`, same convention
    /// as [`Self::centroid_median`]).
    ///
    /// Derived from [`Self::centroid_median`] by subtracting `3A` from both
    /// sides at the scalar level (`mul_sub_right_proof` plus the
    /// `mul three a ~ mul two a + a` bridge, `add_middle_swap_proof` for the
    /// final rearrangement), not restated or reproved from scratch. No
    /// hypothesis, no `inv3`, unconditional for every configuration.
    pub centroid_ratio: NameId,
    /// **Leibniz's centroid formula.** `∀ P A B C,
    /// Equiv (add (distSq P A) (add (distSq P B) (distSq P C)))
    ///       (add (add (add (distSq P G) (distSq P G)) (distSq P G))
    ///            (add (distSq G A) (add (distSq G B) (distSq G C))))`,
    /// where `G := centroid A B C` (`3X` spelled `(X+X)+X`).
    ///
    /// The centroid's defining variational property: the sum of squared
    /// distances from any point `P` to the three vertices equals three times
    /// the squared distance to the centroid, plus the sum of squared
    /// distances from the centroid to the vertices. No hypothesis,
    /// unconditional for every `P,A,B,C` — the cross terms `dot(P-G, X-G)`
    /// summed over `X ∈ {A,B,C}` vanish because `(A-G)+(B-G)+(C-G) ~ 0`,
    /// which is exactly `3G ~ A+B+C` rearranged.
    pub centroid_dist_sq: NameId,
    /// `CPoint.Scalar.lerp a b t := CReal.add a (CReal.mul t (CReal.add b (CReal.neg a)))`
    /// — the cevian parametrisation, `a + t·(b−a)`, mirroring how
    /// [`Self::midpoint`] is built one level up (`midpoint` is the special
    /// case `t := inv2`, though this file does not derive one from the
    /// other).
    pub lerp_scalar: NameId,
    /// `CPoint.lerp P Q t := CPoint.mk (Scalar.lerp (x P) (x Q) t) (Scalar.lerp
    /// (y P) (y Q) t)` — the point on segment `PQ` at parameter `t`.
    pub point_lerp: NameId,
    /// `CPoint.lerp_zero : ∀ B C, CPoint.Equiv (lerp B C CReal.zero) B`.
    pub lerp_zero: NameId,
    /// `CPoint.lerp_one : ∀ B C, CPoint.Equiv (lerp B C CReal.one) C`.
    pub lerp_one: NameId,
    /// `CPoint.lerp_half_is_midpoint : ∀ B C,
    /// CPoint.Equiv (lerp B C inv2) (point_midpoint B C)` — ties the new
    /// construction to the existing one; the check that `lerp` is the right
    /// definition, not just *some* interpolation of `B` and `C`.
    pub lerp_half_is_midpoint: NameId,
    /// **The algebraic engine.** `CPoint.lerp_dist_sq : ∀ P B C t,
    /// Equiv (distSq P (lerp B C t))
    ///   (add (distSq P B)
    ///        (add (neg (mul t (dot (sub P B) (sub C B))))
    ///             (add (neg (mul t (dot (sub P B) (sub C B))))
    ///                  (mul t (mul t (distSq B C))))))`,
    /// i.e. `|PD|² = |PB|² − 2t·(P−B)·(C−B) + t²·|BC|²` where `D := lerp B C
    /// t`. Proved by telescoping `P − D ~ (P−B) − (D−B)` through `B`
    /// (`diff_diff_scalar_proof`) and expanding via [`Self::dot_self_sub`];
    /// the `t²`/`t·` coefficients come from `D − B ~ t·(C−B)`
    /// (`add_sub_cancel_left` applied to `lerp`'s own definition) pulled
    /// through `dot`'s bilinearity. No hypothesis on `t` — this holds for
    /// every scalar, not just `t ∈ [0,1]`.
    pub lerp_dist_sq: NameId,
    /// **Stewart's theorem, squared/parametric form.** `CPoint.stewart : ∀ A B
    /// C t,
    /// Equiv (add (distSq A (lerp B C t)) (mul t (mul (add one (neg t)) (distSq B C))))
    ///       (add (mul (add one (neg t)) (distSq A B)) (mul t (distSq A C)))`,
    /// i.e. `|AD|² + t(1−t)|BC|² ~ (1−t)|AB|² + t|AC|²` where `D := lerp B C
    /// t`. This is the classical Stewart identity with every unsigned length
    /// (`BD, DC, BC`) replaced by its squared/parametric equivalent — this
    /// kernel has no `CReal.sqrt`, only `natSqrt`, so the literal
    /// length-product statement `BD·DC·BC + AD²·BC ~ AB²·DC + AC²·BD` is not
    /// available. Multiplying this identity through by the (unsquared) `BC`
    /// recovers exactly that classical form when `t := BD/BC`; this theorem
    /// is the honest target, not that one. Apollonius' median theorem
    /// ([`Self::apollonius_median`]) is the `t := inv2` case (up to the
    /// `t(1−t) = 1/4` and `1−t = t = 1/2` simplifications, not derived here).
    /// Proved from [`Self::lerp_dist_sq`] at `P := A` plus one more
    /// `dot_self_sub`-through-`B` expansion relating the cross term to
    /// `distSq A C`, then pure `CReal` ring algebra in the four opaque
    /// quantities `distSq A B`, `dot (sub A B) (sub C B)`, `distSq B C`, `t`.
    pub stewart: NameId,
    /// **The median corollary of Stewart.** `∀ A B C,
    /// Equiv (add (distSq A M) (mul inv2 (mul inv2 (distSq B C))))
    ///       (add (mul inv2 (distSq A B)) (mul inv2 (distSq A C)))`,
    /// where `M := point_midpoint B C`.
    ///
    /// [`Self::stewart`] instantiated at `t := inv2`, then rewritten through
    /// [`Self::lerp_half_is_midpoint`] (`lerp B C inv2 ~ M`) and
    /// [`Self::one_sub_inv2`] (`1 − inv2 ~ inv2`, applied to both `mul (add
    /// one (neg inv2)) …` factors `stewart` produces at this `t`). **Not
    /// textually [`Self::apollonius_median`]**: doubling this identity and
    /// eliminating `distSq A M`'s sibling `distSq B M` through the (unbuilt)
    /// identity `distSq B M ~ mul inv2 (mul inv2 (distSq B C))` recovers
    /// `apollonius_median` exactly (`BM² = ¼BC²` is what bridges "distance to
    /// the midpoint" and "distance between the endpoints") — the two
    /// theorems are the same fact under that bridge, not proved one from the
    /// other in this file.
    pub stewart_median: NameId,
    /// **The circumcentre identity, unconditional.** `∀ O A B C,
    /// Equiv (add (add (distSq O A) (neg (distSq O B))) (add (add (distSq O B)
    /// (neg (distSq O C))) (add (distSq O C) (neg (distSq O A)))))
    /// CReal.zero`.
    ///
    /// Mirrors [`Self::orthocentre_identity`]'s shape exactly: a
    /// hypothesis-free 3-term cyclic sum, always zero, purely because `(x-y) +
    /// ((y-z)+(z-x)) ~ 0` for any three `CReal`s — here `x,y,z :=` the three
    /// squared distances from `O`. [`Self::circumcentre_third_distance`] is
    /// what makes it usable the way [`Self::orthocentre_third_altitude`] uses
    /// `orthocentre_identity`.
    pub circumcentre_identity: NameId,
    /// **Concurrence of the two circumcentre equalities.** `∀ O A B C,
    /// Equiv (distSq O A) (distSq O B) → Equiv (distSq O B) (distSq O C) →
    /// Equiv (distSq O A) (distSq O C)`.
    ///
    /// Immediate from [`Self::circumcentre_identity`] exactly the way
    /// [`Self::orthocentre_third_altitude`] is immediate from
    /// `orthocentre_identity`: the two hypotheses make the first two summands
    /// of that cyclic sum vanish, so the third must too, and unwinding the
    /// third summand (`distSq O C − distSq O A ~ 0`) gives the stated
    /// conclusion. (A direct `CReal.Equiv` transitivity proof would be
    /// shorter; this route is taken to keep the same two-lemma shape as the
    /// orthocentre pair.)
    pub circumcentre_third_distance: NameId,
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
    declare_one_sub_inv2(&mut d, p)?;
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
    declare_orthocentre_identity(&mut d, p)?;
    declare_orthocentre_third_altitude(&mut d, p)?;
    declare_dist_sq(&mut d, p)?;
    declare_dist_sq_congr(&mut d, p)?;
    declare_dist_sq_comm(&mut d, p)?;
    declare_dist_sq_self_zero(&mut d, p)?;
    declare_circumcentre_identity(&mut d, p)?;
    declare_circumcentre_third_distance(&mut d, p)?;
    declare_pythagoras_dist_sq(&mut d, p)?;
    declare_parallelogram_diagonals_bisect(&mut d, p)?;
    declare_parallelogram_opposite_sides_eq(&mut d, p)?;
    declare_dot_self_add(&mut d, p)?;
    declare_dot_self_sub(&mut d, p)?;
    declare_dot_self_add3(&mut d, p)?;
    declare_parallelogram_law(&mut d, p)?;
    declare_euler_quadrilateral(&mut d, p)?;
    declare_apollonius_median(&mut d, p)?;
    declare_three(&mut d, p)?;
    declare_inv3(&mut d, p)?;
    declare_centroid_scalar(&mut d, p)?;
    declare_centroid_scalar_self(&mut d, p)?;
    declare_centroid(&mut d, p)?;
    declare_centroid_median(&mut d, p)?;
    declare_centroid_ratio(&mut d, p)?;
    declare_centroid_dist_sq(&mut d, p)?;
    declare_lerp_scalar(&mut d, p)?;
    declare_point_lerp(&mut d, p)?;
    declare_lerp_zero(&mut d, p)?;
    declare_lerp_one(&mut d, p)?;
    declare_lerp_half_is_midpoint(&mut d, p)?;
    declare_lerp_dist_sq(&mut d, p)?;
    declare_stewart(&mut d, p)?;
    declare_stewart_median(&mut d, p)?;
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
        one_sub_inv2: kernel.name_str(scalar, "one_sub_inv2"),
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
        orthocentre_identity: kernel.name_str(point, "orthocentre_identity"),
        orthocentre_third_altitude: kernel.name_str(point, "orthocentre_third_altitude"),
        dist_sq: kernel.name_str(point, "distSq"),
        dist_sq_congr: kernel.name_str(point, "distSq_congr"),
        dist_sq_comm: kernel.name_str(point, "distSq_comm"),
        dist_sq_self_zero: kernel.name_str(point, "distSq_self_zero"),
        pythagoras_dist_sq: kernel.name_str(point, "pythagoras_distSq"),
        parallelogram_diagonals_bisect: kernel.name_str(point, "parallelogram_diagonals_bisect"),
        parallelogram_opposite_sides_eq: kernel.name_str(point, "parallelogram_opposite_sides_eq"),
        dot_self_add: kernel.name_str(point, "dot_self_add"),
        dot_self_sub: kernel.name_str(point, "dot_self_sub"),
        dot_self_add3: kernel.name_str(point, "dot_self_add3"),
        parallelogram_law: kernel.name_str(point, "parallelogram_law"),
        euler_quadrilateral: kernel.name_str(point, "euler_quadrilateral"),
        apollonius_median: kernel.name_str(point, "apollonius_median"),
        three: kernel.name_str(scalar, "three"),
        three_pos_bound: kernel.name_str(scalar, "threePosBound"),
        inv3: kernel.name_str(scalar, "inv3"),
        centroid_scalar: kernel.name_str(scalar, "centroid"),
        centroid_scalar_self: kernel.name_str(scalar, "centroid_self"),
        centroid: kernel.name_str(point, "centroid"),
        centroid_median: kernel.name_str(point, "centroid_median"),
        centroid_ratio: kernel.name_str(point, "centroid_ratio"),
        centroid_dist_sq: kernel.name_str(point, "centroid_distSq"),
        lerp_scalar: kernel.name_str(scalar, "lerp"),
        point_lerp: kernel.name_str(point, "lerp"),
        lerp_zero: kernel.name_str(point, "lerp_zero"),
        lerp_one: kernel.name_str(point, "lerp_one"),
        lerp_half_is_midpoint: kernel.name_str(point, "lerp_half_is_midpoint"),
        lerp_dist_sq: kernel.name_str(point, "lerp_dist_sq"),
        stewart: kernel.name_str(point, "stewart"),
        stewart_median: kernel.name_str(point, "stewart_median"),
        circumcentre_identity: kernel.name_str(point, "circumcentre_identity"),
        circumcentre_third_distance: kernel.name_str(point, "circumcentre_third_distance"),
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

/// `CPoint.Equiv pt pt`, built directly from `Equiv.refl` on each coordinate
/// (there is no standalone `point_equiv_refl` theorem in this file — every
/// other spot that needs one already has a hypothesis or an `and_intro` of
/// two concrete per-coordinate facts to hand instead).
fn point_equiv_refl(d: &mut IntDev<'_>, p: CPointPrelude, pt: ExprId) -> ExprId {
    let px = d.const_app(p.x, &[pt]);
    let py = d.const_app(p.y, &[pt]);
    let claim_x = equiv(d, p, px, px);
    let claim_y = equiv(d, p, py, py);
    let refl_x = refl(d, p, px);
    let refl_y = refl(d, p, py);
    and_intro(d, p, claim_x, claim_y, refl_x, refl_y)
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

/// Given `h : Equiv (add b (neg a)) (add c (neg dd))` [`b - a ~ c - d`],
/// produce `Equiv (mul inv2 (add a c)) (mul inv2 (add b dd))`
/// [`midpoint a c ~ midpoint b d`] — the scalar content of
/// [`CPointPrelude::parallelogram_diagonals_bisect`].
///
/// Same shape of argument as [`sum_swap_proof`] (add `a + d` to both sides of
/// `h` and reduce each side by cancellation), but pointed the other way: that
/// lemma turns a sum identity into a difference identity, this one turns a
/// difference identity into a sum identity, which is then lifted through
/// [`CPointPrelude::inv2`] by one `mul_congr` step.
fn diag_bisect_midpoint_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let na = cneg(d, p, a);
    let ndd = cneg(d, p, dd);
    let big_x = cadd(d, p, b, na); // X = b + (-a)
    let big_y = cadd(d, p, c, ndd); // Y = c + (-d)
    let big_z = cadd(d, p, a, dd); // Z = a + d
    let bd = cadd(d, p, b, dd);
    let ac = cadd(d, p, a, c);

    // x_reduce : Equiv (add X Z) bd  —  (b + -a) + (a + dd) ~ b + dd.
    let x_reduce = {
        let xz = cadd(d, p, big_x, big_z);
        let inner1 = cadd(d, p, na, big_z); // -a + (a+dd)
        let b_inner1 = cadd(d, p, b, inner1);
        let assoc1 = d.lemma(creal.add_assoc, &[b, na, big_z]); // Equiv(xz, b_inner1)

        let na_a = cadd(d, p, na, a);
        let na_a_dd = cadd(d, p, na_a, dd);
        let assoc2 = d.lemma(creal.add_assoc, &[na, a, dd]); // Equiv(na_a_dd, inner1)
        let step_inner1 = symm(d, p, na_a_dd, inner1, assoc2); // Equiv(inner1, na_a_dd)
        let cancel_a = neg_add_cancel_proof(d, p, a); // Equiv(na_a, zero)
        let zero = czero(d, p);
        let zero_dd = cadd(d, p, zero, dd);
        let refl_dd = refl(d, p, dd);
        let congr_a = d.lemma(creal.add_congr, &[na_a, zero, dd, dd, cancel_a, refl_dd]);
        let za = zero_add_proof(d, p, dd); // Equiv(zero_dd, dd)
        let inner1_reduce = chain(
            d,
            p,
            inner1,
            &[(na_a_dd, step_inner1), (zero_dd, congr_a), (dd, za)],
        );

        let refl_b = refl(d, p, b);
        let congr_b = d.lemma(creal.add_congr, &[b, b, inner1, dd, refl_b, inner1_reduce]); // Equiv(b_inner1, bd)
        chain(d, p, xz, &[(b_inner1, assoc1), (bd, congr_b)])
    };

    // y_reduce : Equiv (add Y Z) ac  —  (c + -dd) + (a + dd) ~ a + c.
    let y_reduce = {
        let yz = cadd(d, p, big_y, big_z);
        let inner2 = cadd(d, p, ndd, big_z); // -dd + (a+dd)
        let c_inner2 = cadd(d, p, c, inner2);
        let assoc3 = d.lemma(creal.add_assoc, &[c, ndd, big_z]); // Equiv(yz, c_inner2)

        let dd_a = cadd(d, p, dd, a);
        let comm_add = d.lemma(creal.add_comm, &[a, dd]); // Equiv(big_z, dd_a)
        let ndd_dda = cadd(d, p, ndd, dd_a);
        let refl_ndd = refl(d, p, ndd);
        let congr_ndd = d.lemma(
            creal.add_congr,
            &[ndd, ndd, big_z, dd_a, refl_ndd, comm_add],
        ); // Equiv(inner2, ndd_dda)

        let ndd_dd = cadd(d, p, ndd, dd);
        let ndd_dd_a = cadd(d, p, ndd_dd, a);
        let assoc4 = d.lemma(creal.add_assoc, &[ndd, dd, a]); // Equiv(ndd_dd_a, ndd_dda)
        let step_ndd_dda = symm(d, p, ndd_dd_a, ndd_dda, assoc4); // Equiv(ndd_dda, ndd_dd_a)

        let cancel_dd = neg_add_cancel_proof(d, p, dd); // Equiv(ndd_dd, zero)
        let zero = czero(d, p);
        let zero_a = cadd(d, p, zero, a);
        let refl_a2 = refl(d, p, a);
        let congr_ndd2 = d.lemma(creal.add_congr, &[ndd_dd, zero, a, a, cancel_dd, refl_a2]);
        let za2 = zero_add_proof(d, p, a); // Equiv(zero_a, a)
        let inner2_reduce = chain(
            d,
            p,
            inner2,
            &[
                (ndd_dda, congr_ndd),
                (ndd_dd_a, step_ndd_dda),
                (zero_a, congr_ndd2),
                (a, za2),
            ],
        );

        let ca = cadd(d, p, c, a);
        let refl_c = refl(d, p, c);
        let congr_c = d.lemma(creal.add_congr, &[c, c, inner2, a, refl_c, inner2_reduce]); // Equiv(c_inner2, ca)
        let comm_ca = d.lemma(creal.add_comm, &[c, a]); // Equiv(ca, ac)
        chain(
            d,
            p,
            yz,
            &[(c_inner2, assoc3), (ca, congr_c), (ac, comm_ca)],
        )
    };

    let refl_z = refl(d, p, big_z);
    let congr_xz_yz = d.lemma(creal.add_congr, &[big_x, big_y, big_z, big_z, h, refl_z]); // Equiv(X+Z, Y+Z)

    let xz = cadd(d, p, big_x, big_z);
    let yz = cadd(d, p, big_y, big_z);
    let bd_symm = symm(d, p, xz, bd, x_reduce); // Equiv(bd, X+Z)
    let combined = chain(
        d,
        p,
        bd,
        &[(xz, bd_symm), (yz, congr_xz_yz), (ac, y_reduce)],
    ); // Equiv(bd, ac)
    let ac_bd = symm(d, p, bd, ac, combined); // Equiv(ac, bd)

    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let refl_inv2 = refl(d, p, inv2);
    d.lemma(creal.mul_congr, &[inv2, inv2, ac, bd, refl_inv2, ac_bd]) // Equiv(midpoint a c, midpoint b dd)
}

/// `Equiv (add cx (neg dx)) (neg (add ax (neg bx)))` — `C - D ~ -(A - B)`,
/// given `h : Equiv (add bx (neg ax)) (add cx (neg dx))` [`B - A ~ C - D`,
/// the raw parallelogram hypothesis on one coordinate]. The scalar content
/// behind [`CPointPrelude::parallelogram_opposite_sides_eq`]'s `CD ~ -(AB)`
/// step: `neg_sub_comm_scalar_proof` turns the hypothesis's `B-A` into
/// `-(A-B)`, and the rest is `symm`/`chain` bookkeeping.
fn opposite_side_neg_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    ax: ExprId,
    bx: ExprId,
    cx: ExprId,
    dx: ExprId,
    h: ExprId,
) -> ExprId {
    let neg_bx = cneg(d, p, bx);
    let ux = cadd(d, p, ax, neg_bx); // A - B
    let neg_ax = cneg(d, p, ax);
    let ba_x = cadd(d, p, bx, neg_ax); // B - A
    let neg_dx = cneg(d, p, dx);
    let wx = cadd(d, p, cx, neg_dx); // C - D
    let neg_ux = cneg(d, p, ux);

    let nsc = neg_sub_comm_scalar_proof(d, p, ax, bx); // Equiv(neg_ux, ba_x)
    let nsc_symm = symm(d, p, neg_ux, ba_x, nsc); // Equiv(ba_x, neg_ux)
    let h_symm = symm(d, p, ba_x, wx, h); // Equiv(wx, ba_x)
    chain(d, p, wx, &[(ba_x, h_symm), (neg_ux, nsc_symm)]) // Equiv(wx, neg_ux)
}

/// `Equiv (add dx (neg ax)) (neg (add bx (neg cx)))` — `D - A ~ -(B - C)`,
/// given `hw : Equiv (add cx (neg dx)) (neg (add ax (neg bx)))`
/// [`C - D ~ -(A - B)`, i.e. `opposite_side_neg_scalar_proof`'s conclusion
/// on the same four coordinates] — the scalar content behind
/// [`CPointPrelude::parallelogram_opposite_sides_eq`]'s `DA ~ -(BC)` step.
///
/// Pure ring algebra plus `hw`: `A - D ~ (A-C)+(C-D) ~ (A-B)+(B-C)+(C-D)`
/// (`telescope_scalar_proof` twice), the last summand cancels the first
/// against `hw` (`add_sub_cancel_left`) leaving `B - C`, then
/// `neg_sub_comm_scalar_proof` turns `D - A ~ -(A - D)` into the claim.
fn diag_side_neg_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    ax: ExprId,
    bx: ExprId,
    cx: ExprId,
    dx: ExprId,
    hw: ExprId,
) -> ExprId {
    let creal = p.creal;
    let neg_bx = cneg(d, p, bx);
    let ux = cadd(d, p, ax, neg_bx); // A - B
    let neg_cx = cneg(d, p, cx);
    let vx = cadd(d, p, bx, neg_cx); // B - C
    let neg_dx = cneg(d, p, dx);
    let wx = cadd(d, p, cx, neg_dx); // C - D
    let neg_ax = cneg(d, p, ax);
    let zx = cadd(d, p, dx, neg_ax); // D - A
    let neg_ux = cneg(d, p, ux);

    let ax_cx = cadd(d, p, ax, neg_cx); // A - C
    let telescope1 = telescope_scalar_proof(d, p, ax, cx, dx); // Equiv(ax_dx, add ax_cx wx)
    let telescope2 = telescope_scalar_proof(d, p, ax, bx, cx); // Equiv(ax_cx, add ux vx)
    let refl_wx = refl(d, p, wx);
    let uxvx = cadd(d, p, ux, vx);
    let combine1 = d.lemma(creal.add_congr, &[ax_cx, uxvx, wx, wx, telescope2, refl_wx]); // Equiv(ax_cx+wx, uxvx+wx)

    let refl_uxvx = refl(d, p, uxvx);
    let congr_w = d.lemma(creal.add_congr, &[uxvx, uxvx, wx, neg_ux, refl_uxvx, hw]); // Equiv(uxvx+wx, uxvx+neg_ux)
    let cancel = add_sub_cancel_left(d, p, ux, vx); // Equiv(uxvx+neg_ux, vx)

    let ax_dx = cadd(d, p, ax, neg_dx);
    let ax_cx_wx = cadd(d, p, ax_cx, wx);
    let uxvx_wx = cadd(d, p, uxvx, wx);
    let uxvx_negux = cadd(d, p, uxvx, neg_ux);
    let ax_dx_to_vx = chain(
        d,
        p,
        ax_dx,
        &[
            (ax_cx_wx, telescope1),
            (uxvx_wx, combine1),
            (uxvx_negux, congr_w),
            (vx, cancel),
        ],
    ); // Equiv(ax_dx, vx)

    let neg_ax_dx = cneg(d, p, ax_dx);
    let nsc_ad = neg_sub_comm_scalar_proof(d, p, ax, dx); // Equiv(neg_ax_dx, zx)
    let zx_via_neg = symm(d, p, neg_ax_dx, zx, nsc_ad); // Equiv(zx, neg_ax_dx)
    let neg_congr_adv = d.lemma(creal.neg_congr, &[ax_dx, vx, ax_dx_to_vx]); // Equiv(neg_ax_dx, neg_vx)
    let neg_vx = cneg(d, p, vx);

    chain(
        d,
        p,
        zx,
        &[(neg_ax_dx, zx_via_neg), (neg_vx, neg_congr_adv)],
    ) // Equiv(zx, neg_vx)
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

/// `Equiv (add c (neg m)) (neg (add b (neg m)))` — `c - m ~ -(b - m)`, given
/// `m` is literally built as `midpoint b c` (so `Equiv m (midpoint b c)`
/// holds by `refl`, and [`double_o_eq_a_plus_b_proof`] needs no separate
/// hypothesis to fire). The bridge [`declare_apollonius_median`] needs to
/// turn a triangle's two sides into a common pair of vectors from the
/// midpoint of the third.
fn apollonius_neg_swap_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    b: ExprId,
    c: ExprId,
    m: ExprId,
) -> ExprId {
    let creal = p.creal;
    let refl_m = refl(d, p, m);
    let double_fact = double_o_eq_a_plus_b_proof(d, p, b, c, m, refl_m); // Equiv(m+m, b+c)
    let mm = cadd(d, p, m, m);
    let bc = cadd(d, p, b, c);
    let cb = cadd(d, p, c, b);
    let comm_bc = d.lemma(creal.add_comm, &[b, c]); // Equiv(bc, cb)
    let h_prime = chain(d, p, mm, &[(bc, double_fact), (cb, comm_bc)]); // Equiv(m+m, c+b)
    let swap = sum_swap_proof(d, p, m, m, c, b, h_prime); // Equiv(c-m, m-b)
    let nb = cneg(d, p, b);
    let nm = cneg(d, p, m);
    let b_nm = cadd(d, p, b, nm); // b - m
    let neg_b_nm = cneg(d, p, b_nm); // -(b-m)
    let m_nb = cadd(d, p, m, nb); // m - b
    let negsubcomm = neg_sub_comm_scalar_proof(d, p, b, m); // Equiv(neg(b-m), m-b)
    let negsubcomm_symm = symm(d, p, neg_b_nm, m_nb, negsubcomm); // Equiv(m-b, neg(b-m))
    let c_nm = cadd(d, p, c, nm); // c - m
    chain(d, p, c_nm, &[(m_nb, swap), (neg_b_nm, negsubcomm_symm)])
}

/// Given opaque `CReal` terms `x, y, z`, proves
/// `Equiv (add (add x (add (neg y) (add (neg y) z))) (add x (add y (add y z))))
///        (add (add x x) (add z z))`,
/// i.e. `(x - 2y + z) + (x + 2y + z) ~ 2x + 2z` (`2X` written `X+X`) — pure
/// `CReal` ring algebra in three opaque terms, the combination step
/// [`CPointPrelude::apollonius_median`] needs after expanding `distSq A B`
/// via [`CPointPrelude::dot_self_sub`] and `distSq A C` via
/// [`CPointPrelude::dot_self_add`], both at `(sub A M, sub B M)`:
/// `x := dot(sub A M, sub A M)`, `y := dot(sub A M, sub B M)`,
/// `z := dot(sub B M, sub B M)`.
fn apollonius_combine_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ny = cneg(d, p, y);
    let ny_z = cadd(d, p, ny, z); // -y + z
    let a_ = cadd(d, p, ny, ny_z); // -y + (-y + z)
    let term_sub = cadd(d, p, x, a_); // x + (-y + (-y + z))

    let y_z = cadd(d, p, y, z); // y + z
    let b_ = cadd(d, p, y, y_z); // y + (y + z)
    let term_add = cadd(d, p, x, b_); // x + (y + (y + z))

    let lhs = cadd(d, p, term_sub, term_add);

    // swap1 : lhs ~ (x+x) + (a_+b_)
    let swap1 = add_middle_swap_proof(d, p, x, a_, x, b_);
    let xx = cadd(d, p, x, x);
    let ab_ = cadd(d, p, a_, b_);
    let after_swap1 = cadd(d, p, xx, ab_);

    // inner_reduce : Equiv((-y+z)+(y+z), z+z)
    let nyy = cadd(d, p, ny, y);
    let zz = cadd(d, p, z, z);
    let nyz_yz = cadd(d, p, ny_z, y_z);
    let swap3 = add_middle_swap_proof(d, p, ny, z, y, z); // nyz_yz ~ nyy+zz
    let nyy_zz = cadd(d, p, nyy, zz);
    let cancel = neg_add_cancel_proof(d, p, y); // Equiv(nyy, zero)
    let zero = czero(d, p);
    let refl_zz = refl(d, p, zz);
    let congr3 = d.lemma(creal.add_congr, &[nyy, zero, zz, zz, cancel, refl_zz]); // nyy_zz ~ zero+zz
    let zero_zz = cadd(d, p, zero, zz);
    let za = zero_add_proof(d, p, zz); // zero+zz ~ zz
    let inner_reduce = chain(
        d,
        p,
        nyz_yz,
        &[(nyy_zz, swap3), (zero_zz, congr3), (zz, za)],
    );

    // ab_ ~ zz
    let swap2 = add_middle_swap_proof(d, p, ny, ny_z, y, y_z); // ab_ ~ nyy + nyz_yz
    let nyy_nyzyz = cadd(d, p, nyy, nyz_yz);
    let congr2 = d.lemma(
        creal.add_congr,
        &[nyy, zero, nyz_yz, zz, cancel, inner_reduce],
    ); // nyy_nyzyz ~ zero_zz
    let ab_reduce = chain(
        d,
        p,
        ab_,
        &[(nyy_nyzyz, swap2), (zero_zz, congr2), (zz, za)],
    );

    // combine: after_swap1 ~ (x+x)+(z+z)
    let refl_xx = refl(d, p, xx);
    let combined = d.lemma(creal.add_congr, &[xx, xx, ab_, zz, refl_xx, ab_reduce]);
    let target = cadd(d, p, xx, zz);

    chain(d, p, lhs, &[(after_swap1, swap1), (target, combined)])
}

/// Raw `CReal.mul inv3 (CReal.add a (CReal.add b c))` — definitionally
/// `Scalar.centroid a b c`, built inline (mirroring how [`double_midpoint_proof`]
/// builds `mul inv2 (add a b)` inline instead of calling the named
/// [`midpoint`] helper) so the ring-algebra steps below can manipulate it
/// syntactically.
fn ccentroid_raw(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let inv3 = d.kernel().const_(p.inv3, vec![]);
    let bc = cadd(d, p, b, c);
    let s = cadd(d, p, a, bc);
    cmul(d, p, inv3, s)
}

/// `Equiv (mul three x) (add (add x x) x)` — `3x` spelled `(x+x)+x`, the
/// `three := add two one` sibling of [`two_mul_eq_double_proof`].
fn three_mul_eq_triple_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    let creal = p.creal;
    let two = d.kernel().const_(p.two, vec![]);
    let one = d.kernel().const_(creal.one, vec![]);
    let three = d.kernel().const_(p.three, vec![]);
    let mul_three_x = cmul(d, p, three, x);
    let mul_two_x = cmul(d, p, two, x);
    let mul_one_x = cmul(d, p, one, x);
    let sum_muls = cadd(d, p, mul_two_x, mul_one_x);

    // mul three x = mul (add two one) x ~ (mul two x) + (mul one x), since
    // `three` unfolds to `add two one`.
    let rd = right_distrib_proof(d, p, two, one, x); // Equiv(mul (add two one) x, sum_muls)

    let double_x = two_mul_eq_double_proof(d, p, x); // Equiv(mul_two_x, add x x)
    let xx = cadd(d, p, x, x);

    let mul_x_one = cmul(d, p, x, one);
    let comm = d.lemma(creal.mul_comm, &[one, x]); // Equiv(mul_one_x, mul_x_one)
    let mo = d.lemma(creal.mul_one, &[x]); // Equiv(mul_x_one, x)
    let one_x = chain(d, p, mul_one_x, &[(mul_x_one, comm), (x, mo)]); // Equiv(mul_one_x, x)

    let congr = d.lemma(
        creal.add_congr,
        &[mul_two_x, xx, mul_one_x, x, double_x, one_x],
    ); // Equiv(sum_muls, add xx x)
    let xx_x = cadd(d, p, xx, x);
    chain(d, p, mul_three_x, &[(sum_muls, rd), (xx_x, congr)])
}

/// `Equiv (mul three (centroid_scalar a b c)) (add a (add b c))` — `3G ~
/// a+(b+c)`, the `three`/`inv3` sibling of [`double_midpoint_proof`].
fn triple_g_eq_sum_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let creal = p.creal;
    let three = d.kernel().const_(p.three, vec![]);
    let inv3 = d.kernel().const_(p.inv3, vec![]);
    let bc = cadd(d, p, b, c);
    let s = cadd(d, p, a, bc);
    let mid = cmul(d, p, inv3, s); // =defeq= centroid_scalar a b c
    let three_mid = cmul(d, p, three, mid);
    let three_inv3 = cmul(d, p, three, inv3);
    let three_inv3_s = cmul(d, p, three_inv3, s);
    let zero_nat = d.num(0);
    let h_three = d.kernel().const_(p.three_pos_bound, vec![]);

    let assoc = d.lemma(creal.mul_assoc, &[three, inv3, s]); // Equiv(three_inv3_s, three_mid)
    let step_a = symm(d, p, three_inv3_s, three_mid, assoc); // Equiv(three_mid, three_inv3_s)
    let cancel = d.lemma(creal.mul_inv_cancel, &[three, zero_nat, h_three]); // Equiv(three_inv3, one)
    let one = d.kernel().const_(creal.one, vec![]);
    let refl_s = refl(d, p, s);
    let congr1 = d.lemma(creal.mul_congr, &[three_inv3, one, s, s, cancel, refl_s]); // Equiv(three_inv3_s, mul one s)
    let mul_one_s = cmul(d, p, one, s);
    let comm = d.lemma(creal.mul_comm, &[one, s]); // Equiv(mul_one_s, mul s one)
    let mul_s_one = cmul(d, p, s, one);
    let mo = d.lemma(creal.mul_one, &[s]); // Equiv(mul_s_one, s)
    let one_mul_s = chain(d, p, mul_one_s, &[(mul_s_one, comm), (s, mo)]);

    chain(
        d,
        p,
        three_mid,
        &[(three_inv3_s, step_a), (mul_one_s, congr1), (s, one_mul_s)],
    )
}

/// Per-coordinate content of [`CPointPrelude::centroid_median`]: given
/// `va,vb,vc`, with `g := ccentroid_raw va vb vc` and `m := mul inv2 (add vb
/// vc)` (both raw, definitionally `Scalar.centroid`/`Scalar.midpoint`),
/// proves `Equiv (add (add g g) g) (add va (add m m))` — `3G ~ A + 2M`.
fn centroid_median_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    va: ExprId,
    vb: ExprId,
    vc: ExprId,
) -> ExprId {
    let creal = p.creal;
    let g = ccentroid_raw(d, p, va, vb, vc);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let bc = cadd(d, p, vb, vc);
    let m = cmul(d, p, inv2, bc); // raw =defeq= midpoint vb vc

    // (g+g)+g ~ mul three g  (reverse of three_mul_eq_triple_proof)
    let three = d.kernel().const_(p.three, vec![]);
    let mul_three_g = cmul(d, p, three, g);
    let gg = cadd(d, p, g, g);
    let gg_g = cadd(d, p, gg, g);
    let ta = three_mul_eq_triple_proof(d, p, g); // Equiv(mul_three_g, gg_g)
    let ta_symm = symm(d, p, mul_three_g, gg_g, ta); // Equiv(gg_g, mul_three_g)

    // mul three g ~ va + (vb+vc)
    let sum_fact = triple_g_eq_sum_proof(d, p, va, vb, vc); // Equiv(mul_three_g, add va bc)
    let va_bc = cadd(d, p, va, bc);

    // vb+vc ~ mul two m ~ m+m
    let two = d.kernel().const_(p.two, vec![]);
    let mul_two_m = cmul(d, p, two, m);
    let dm = double_midpoint_proof(d, p, vb, vc); // Equiv(mul_two_m, bc)
    let dm_symm = symm(d, p, mul_two_m, bc, dm); // Equiv(bc, mul_two_m)
    let double_m = two_mul_eq_double_proof(d, p, m); // Equiv(mul_two_m, add m m)
    let mm = cadd(d, p, m, m);
    let bc_to_mm = chain(d, p, bc, &[(mul_two_m, dm_symm), (mm, double_m)]); // Equiv(bc, mm)

    let refl_va = refl(d, p, va);
    let congr_va = d.lemma(creal.add_congr, &[va, va, bc, mm, refl_va, bc_to_mm]); // Equiv(va_bc, va+mm)
    let va_mm = cadd(d, p, va, mm);

    chain(
        d,
        p,
        gg_g,
        &[(mul_three_g, ta_symm), (va_bc, sum_fact), (va_mm, congr_va)],
    )
}

/// `Equiv (add (add (sub g a) (sub g a)) (sub g a)) (add (sub m a) (sub m a))`
/// — `3(g-a) ~ 2(m-a)`, `g := ccentroid_raw a b c`, `m := midpoint b c` (raw).
/// Derived from [`centroid_median_scalar_proof`]'s `Equiv((g+g)+g, a+(m+m))`
/// by subtracting `3a` from both sides: `mul_sub_right_proof` turns `mul
/// three (sub g a)` into `mul three g − mul three a`, the bridge `mul three a
/// ~ mul two a + a` (via [`three_mul_eq_triple_proof`]/[`two_mul_eq_double_proof`])
/// lets `add_middle_swap_proof` cancel the shared `a`, and what remains is
/// `mul two m − mul two a = mul two (sub m a)` (`mul_sub_right_proof` again).
fn centroid_ratio_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let creal = p.creal;
    let g = ccentroid_raw(d, p, a, b, c);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let bc = cadd(d, p, b, c);
    let m = cmul(d, p, inv2, bc); // raw =defeq= midpoint b c

    let three = d.kernel().const_(p.three, vec![]);
    let two = d.kernel().const_(p.two, vec![]);

    // mul three g ~ (g+g)+g ~ a+(m+m) ~ a + mul two m.
    let h_cm = centroid_median_scalar_proof(d, p, a, b, c); // Equiv((g+g)+g, a+(m+m))
    let gg = cadd(d, p, g, g);
    let gg_g = cadd(d, p, gg, g);
    let mm = cadd(d, p, m, m);
    let a_mm = cadd(d, p, a, mm);
    let mul_three_g = cmul(d, p, three, g);
    let mte_g = three_mul_eq_triple_proof(d, p, g); // Equiv(mul_three_g, gg_g)
    let mg_a_mm = chain(d, p, mul_three_g, &[(gg_g, mte_g), (a_mm, h_cm)]); // Equiv(mul_three_g, a_mm)

    let mul_two_m = cmul(d, p, two, m);
    let tm = two_mul_eq_double_proof(d, p, m); // Equiv(mul_two_m, m+m)
    let tm_symm = symm(d, p, mul_two_m, mm, tm); // Equiv(mm, mul_two_m)
    let refl_a = refl(d, p, a);
    let congr_a_mm = d.lemma(creal.add_congr, &[a, a, mm, mul_two_m, refl_a, tm_symm]); // Equiv(a_mm, a+mul_two_m)
    let a_mul_two_m = cadd(d, p, a, mul_two_m);
    let mg2 = chain(
        d,
        p,
        mul_three_g,
        &[(a_mm, mg_a_mm), (a_mul_two_m, congr_a_mm)],
    ); // Equiv(mul_three_g, a+mul_two_m)

    // mul three (sub g a) ~ mul_three_g + neg(mul three a) ~ (a+mul_two_m) + neg(mul three a).
    let neg_a = cneg(d, p, a);
    let sub_ga = cadd(d, p, g, neg_a);
    let mul_three_sub_ga = cmul(d, p, three, sub_ga);
    let msr_g = mul_sub_right_proof(d, p, three, g, a); // Equiv(mul_three_sub_ga, add mul_three_g (neg (mul three a)))
    let mul_three_a = cmul(d, p, three, a);
    let neg_mta = cneg(d, p, mul_three_a);
    let mul_three_g_neg_mta = cadd(d, p, mul_three_g, neg_mta);
    let refl_neg_mta = refl(d, p, neg_mta);
    let step_replace = d.lemma(
        creal.add_congr,
        &[
            mul_three_g,
            a_mul_two_m,
            neg_mta,
            neg_mta,
            mg2,
            refl_neg_mta,
        ],
    ); // Equiv(mul_three_g_neg_mta, a_mul_two_m+neg_mta)
    let a_mul_two_m_neg_mta = cadd(d, p, a_mul_two_m, neg_mta);
    let phase1 = chain(
        d,
        p,
        mul_three_sub_ga,
        &[
            (mul_three_g_neg_mta, msr_g),
            (a_mul_two_m_neg_mta, step_replace),
        ],
    ); // Equiv(mul_three_sub_ga, a_mul_two_m_neg_mta)

    // mul three a ~ mul two a + a.
    let mte_a = three_mul_eq_triple_proof(d, p, a); // Equiv(mul_three_a, (a+a)+a)
    let aa = cadd(d, p, a, a);
    let aa_a = cadd(d, p, aa, a);
    let mul_two_a = cmul(d, p, two, a);
    let tm_a = two_mul_eq_double_proof(d, p, a); // Equiv(mul_two_a, a+a)
    let tm_a_symm = symm(d, p, mul_two_a, aa, tm_a); // Equiv(aa, mul_two_a)
    let refl_a2 = refl(d, p, a);
    let congr_replace = d.lemma(creal.add_congr, &[aa, mul_two_a, a, a, tm_a_symm, refl_a2]); // Equiv(aa_a, mul_two_a+a)
    let mul_two_a_a = cadd(d, p, mul_two_a, a);
    let y_eq_za = chain(
        d,
        p,
        mul_three_a,
        &[(aa_a, mte_a), (mul_two_a_a, congr_replace)],
    ); // Equiv(mul_three_a, mul_two_a+a)

    // neg(mul three a) ~ neg a + neg(mul two a).
    let neg_congr_y = d.lemma(creal.neg_congr, &[mul_three_a, mul_two_a_a, y_eq_za]); // Equiv(neg_mta, neg(mul_two_a_a))
    let neg_mul_two_a_a = cneg(d, p, mul_two_a_a);
    let na1 = neg_add_proof(d, p, mul_two_a, a); // Equiv(neg(mul_two_a_a), add(neg mul_two_a)(neg a))
    let neg_mul_two_a = cneg(d, p, mul_two_a);
    let neg_z_neg_a = cadd(d, p, neg_mul_two_a, neg_a);
    let comm_zn = d.lemma(creal.add_comm, &[neg_mul_two_a, neg_a]); // Equiv(negZ+negA, negA+negZ)
    let neg_a_neg_z = cadd(d, p, neg_a, neg_mul_two_a);
    let neg_mta_final = chain(
        d,
        p,
        neg_mta,
        &[
            (neg_mul_two_a_a, neg_congr_y),
            (neg_z_neg_a, na1),
            (neg_a_neg_z, comm_zn),
        ],
    ); // Equiv(neg_mta, neg_a_neg_z)

    // (a+mul_two_m) + neg_mta ~ (a+mul_two_m) + (negA+negZ) ~ (a+negA)+(mul_two_m+negZ).
    let refl_a_x = refl(d, p, a_mul_two_m);
    let step2 = d.lemma(
        creal.add_congr,
        &[
            a_mul_two_m,
            a_mul_two_m,
            neg_mta,
            neg_a_neg_z,
            refl_a_x,
            neg_mta_final,
        ],
    ); // Equiv(a_mul_two_m_neg_mta, a_mul_two_m + neg_a_neg_z)
    let a_x_neg_a_neg_z = cadd(d, p, a_mul_two_m, neg_a_neg_z);

    let swap = add_middle_swap_proof(d, p, a, mul_two_m, neg_a, neg_mul_two_a); // Equiv(a_x_neg_a_neg_z, (a+negA)+(mul_two_m+negZ))
    let a_neg_a = cadd(d, p, a, neg_a);
    let x_neg_z = cadd(d, p, mul_two_m, neg_mul_two_a);
    let swapped = cadd(d, p, a_neg_a, x_neg_z);

    let an_a = d.lemma(creal.add_neg, &[a]); // Equiv(a_neg_a, zero)
    let zero = czero(d, p);
    let refl_xz = refl(d, p, x_neg_z);
    let congr_zero = d.lemma(
        creal.add_congr,
        &[a_neg_a, zero, x_neg_z, x_neg_z, an_a, refl_xz],
    ); // Equiv(swapped, zero+x_neg_z)
    let zero_xz = cadd(d, p, zero, x_neg_z);
    let za = zero_add_proof(d, p, x_neg_z); // Equiv(zero_xz, x_neg_z)

    // x_neg_z ~ mul two (sub m a).
    let neg_a3 = cneg(d, p, a);
    let sub_ma = cadd(d, p, m, neg_a3);
    let mul_two_ma = cmul(d, p, two, sub_ma);
    let msr_m = mul_sub_right_proof(d, p, two, m, a); // Equiv(mul_two_ma, add mul_two_m (neg mul_two_a)) = Equiv(mul_two_ma, x_neg_z)
    let msr_m_symm = symm(d, p, mul_two_ma, x_neg_z, msr_m); // Equiv(x_neg_z, mul_two_ma)

    let final_to_mul_two_ma = chain(
        d,
        p,
        swapped,
        &[
            (zero_xz, congr_zero),
            (x_neg_z, za),
            (mul_two_ma, msr_m_symm),
        ],
    ); // Equiv(swapped, mul_two_ma)

    let mte_ratio = chain(
        d,
        p,
        mul_three_sub_ga,
        &[
            (a_mul_two_m_neg_mta, phase1),
            (a_x_neg_a_neg_z, step2),
            (swapped, swap),
            (mul_two_ma, final_to_mul_two_ma),
        ],
    ); // Equiv(mul_three_sub_ga, mul_two_ma)

    // Convert to the "(X+X)+X ~ Y+Y" additive form.
    let ga_ga = cadd(d, p, sub_ga, sub_ga);
    let x3 = cadd(d, p, ga_ga, sub_ga);
    let three_mte_ga = three_mul_eq_triple_proof(d, p, sub_ga); // Equiv(mul_three_sub_ga, x3)
    let three_mte_ga_symm = symm(d, p, mul_three_sub_ga, x3, three_mte_ga); // Equiv(x3, mul_three_sub_ga)

    let y2 = cadd(d, p, sub_ma, sub_ma);
    let two_mte_ma = two_mul_eq_double_proof(d, p, sub_ma); // Equiv(mul_two_ma, y2)

    chain(
        d,
        p,
        x3,
        &[
            (mul_three_sub_ga, three_mte_ga_symm),
            (mul_two_ma, mte_ratio),
            (y2, two_mte_ma),
        ],
    )
}

/// **The centroid divides each median 2:1, difference form.** See
/// [`CPointPrelude::centroid_ratio`].
fn declare_centroid_ratio(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

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

    let proof_x = centroid_ratio_scalar_proof(d, p, ax, bx, cx);
    let proof_y = centroid_ratio_scalar_proof(d, p, ay, by, cy);

    let gx = ccentroid_raw(d, p, ax, bx, cx);
    let gy = ccentroid_raw(d, p, ay, by, cy);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let bcx = cadd(d, p, bx, cx);
    let mx = cmul(d, p, inv2, bcx);
    let bcy = cadd(d, p, by, cy);
    let my = cmul(d, p, inv2, bcy);

    let claim_x = {
        let neg_ax = cneg(d, p, ax);
        let ga_x = cadd(d, p, gx, neg_ax);
        let ga_ga_x = cadd(d, p, ga_x, ga_x);
        let lhs_x = cadd(d, p, ga_ga_x, ga_x);
        let ma_x = cadd(d, p, mx, neg_ax);
        let rhs_x = cadd(d, p, ma_x, ma_x);
        equiv(d, p, lhs_x, rhs_x)
    };
    let claim_y = {
        let neg_ay = cneg(d, p, ay);
        let ga_y = cadd(d, p, gy, neg_ay);
        let ga_ga_y = cadd(d, p, ga_y, ga_y);
        let lhs_y = cadd(d, p, ga_ga_y, ga_y);
        let ma_y = cadd(d, p, my, neg_ay);
        let rhs_y = cadd(d, p, ma_y, ma_y);
        equiv(d, p, lhs_y, rhs_y)
    };
    let proof = and_intro(d, p, claim_x, claim_y, proof_x, proof_y);

    let big_g = d.const_app(p.centroid, &[pa, pb, pc]);
    let big_m = d.const_app(p.point_midpoint, &[pb, pc]);
    let sub_g_a = psub(d, p, big_g, pa);
    let sub_m_a = psub(d, p, big_m, pa);
    let gg_point = padd(d, p, sub_g_a, sub_g_a);
    let ggg_point = padd(d, p, gg_point, sub_g_a);
    let mm_point = padd(d, p, sub_m_a, sub_m_a);
    let ty_body = d.const_app(p.point_equiv, &[ggg_point, mm_point]);

    let ty = {
        let w2 = d.pi_fv(c_fv, point, ty_body);
        let w1 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(a_fv, point, w1)
    };
    let value = {
        let w2 = d.lam_fv(c_fv, point, proof);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.centroid_ratio,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (add (add a (neg g)) (add (add b (neg g)) (add c (neg g)))) CReal.zero`
/// — `(a-g)+((b-g)+(c-g)) ~ 0`, given `hg : Equiv (add g (add g g)) (add a
/// (add b c))` (`3g ~ a+b+c`). The per-coordinate content behind
/// [`CPointPrelude::centroid_dist_sq`]'s cross-term cancellation: `g` is the
/// centroid's coordinate, so the three vertex-to-centroid vectors sum to
/// zero.
fn triple_sub_sum_zero_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    g: ExprId,
    hg: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ng = cneg(d, p, g);

    // lhs, built from the SAME tree the flatten step below walks, so `lhs`
    // and `sum_tree_build(&lhs_tree)` are the identical `ExprId`.
    let lhs_tree = sadd(
        sadd(SumTree::Leaf(a), SumTree::Leaf(ng)),
        sadd(
            sadd(SumTree::Leaf(b), SumTree::Leaf(ng)),
            sadd(SumTree::Leaf(c), SumTree::Leaf(ng)),
        ),
    );
    let lhs = sum_tree_build(d, p, &lhs_tree); // (a+ng)+((b+ng)+(c+ng))
    let (lhs_chain, lhs_flatten) = flatten_sum_tree(d, p, &lhs_tree); // Equiv(lhs, lhs_chain)

    let mut lhs_leaves = Vec::new();
    sum_tree_leaves(&lhs_tree, &mut lhs_leaves); // [a, ng, b, ng, c, ng]
    let to_leaves = vec![a, b, c, ng, ng, ng];
    let reorder = reorder_right_chain(d, p, &lhs_leaves, &to_leaves); // Equiv(lhs_chain, to_chain)
    let to_chain = build_right_chain(d, p, &to_leaves);

    // Split the flat 6-chain into (a+(b+c)) + (ng+(ng+ng)).
    let abc_chain = build_right_chain(d, p, &[a, b, c]); // a+(b+c)
    let ng_ng_ng = build_right_chain(d, p, &[ng, ng, ng]); // ng+(ng+ng)
    let (concat_result, concat_proof) = concat_right_chains(d, p, &[a, b, c], ng_ng_ng);
    // concat_proof : Equiv(add abc_chain ng_ng_ng, concat_result), and
    // `concat_result` is the same right-chain over [a,b,c,ng,ng,ng] as
    // `to_chain` (both built by the same recursive `cadd` nesting).
    let abc_ngngng = cadd(d, p, abc_chain, ng_ng_ng);
    let split = symm(d, p, abc_ngngng, concat_result, concat_proof); // Equiv(concat_result, abc_ngngng)
    let bridge_to_concat = refl(d, p, concat_result); // to_chain =defeq= concat_result

    // ng+(ng+ng) ~ neg(g+(g+g)), via `neg_add_proof` applied twice.
    let gg = cadd(d, p, g, g);
    let g_gg = cadd(d, p, g, gg);
    let neg_gg = cneg(d, p, gg);
    let neg_g_gg = cneg(d, p, g_gg);
    let step_outer = neg_add_proof(d, p, g, gg); // Equiv(neg_g_gg, add ng neg_gg)
    let ng_neg_gg = cadd(d, p, ng, neg_gg);
    let step_inner = neg_add_proof(d, p, g, g); // Equiv(neg_gg, add ng ng)
    let ng_ng = cadd(d, p, ng, ng);
    let refl_ng = refl(d, p, ng);
    let congr_inner = d.lemma(
        creal.add_congr,
        &[ng, ng, neg_gg, ng_ng, refl_ng, step_inner],
    ); // Equiv(ng_neg_gg, ng+ng_ng)
    let neg_to_ngngng = chain(
        d,
        p,
        neg_g_gg,
        &[(ng_neg_gg, step_outer), (ng_ng_ng, congr_inner)],
    ); // Equiv(neg_g_gg, ng_ng_ng)
    let ngngng_to_neg = symm(d, p, neg_g_gg, ng_ng_ng, neg_to_ngngng); // Equiv(ng_ng_ng, neg_g_gg)

    // (a+(b+c)) + ng_ng_ng ~ (a+(b+c)) + neg(g+(g+g))
    let refl_abc = refl(d, p, abc_chain);
    let congr_outer = d.lemma(
        creal.add_congr,
        &[
            abc_chain,
            abc_chain,
            ng_ng_ng,
            neg_g_gg,
            refl_abc,
            ngngng_to_neg,
        ],
    );
    let abc_neggg = cadd(d, p, abc_chain, neg_g_gg);

    // hg : Equiv(g_gg, abc_chain) -- replace neg(g_gg) with neg(abc_chain).
    let neg_congr_hg = d.lemma(creal.neg_congr, &[g_gg, abc_chain, hg]); // Equiv(neg_g_gg, neg abc_chain)
    let neg_abc = cneg(d, p, abc_chain);
    let refl_abc2 = refl(d, p, abc_chain);
    let congr_final = d.lemma(
        creal.add_congr,
        &[
            abc_chain,
            abc_chain,
            neg_g_gg,
            neg_abc,
            refl_abc2,
            neg_congr_hg,
        ],
    );
    let abc_negabc = cadd(d, p, abc_chain, neg_abc);
    let zero = czero(d, p);
    let an = d.lemma(creal.add_neg, &[abc_chain]); // Equiv(abc_negabc, zero)

    let tail = chain(
        d,
        p,
        abc_ngngng,
        &[
            (abc_neggg, congr_outer),
            (abc_negabc, congr_final),
            (zero, an),
        ],
    );

    chain(
        d,
        p,
        lhs,
        &[
            (lhs_chain, lhs_flatten),
            (to_chain, reorder),
            (concat_result, bridge_to_concat),
            (abc_ngngng, split),
            (zero, tail),
        ],
    )
}

/// `Equiv (add g (add g g)) (add a (add b c))` where `g := ccentroid_raw a b
/// c` — the additive-chain form of [`triple_g_eq_sum_proof`] (`3G` spelled
/// `G+(G+G)` rather than `mul three G`), the shape [`triple_sub_sum_zero_proof`]
/// consumes as its `hg` hypothesis.
fn triple_g_eq_sum_add_form_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let creal = p.creal;
    let g = ccentroid_raw(d, p, a, b, c);
    let three = d.kernel().const_(p.three, vec![]);
    let mul_three_g = cmul(d, p, three, g);
    let gg = cadd(d, p, g, g);
    let g_gg = cadd(d, p, g, gg);
    let gg_g = cadd(d, p, gg, g);

    let ta = three_mul_eq_triple_proof(d, p, g); // Equiv(mul_three_g, gg_g)
    let assoc = d.lemma(creal.add_assoc, &[g, g, g]); // Equiv(gg_g, g_gg)
    let mul_to_g_gg = chain(d, p, mul_three_g, &[(gg_g, ta), (g_gg, assoc)]); // Equiv(mul_three_g, g_gg)
    let mul_to_g_gg_symm = symm(d, p, mul_three_g, g_gg, mul_to_g_gg); // Equiv(g_gg, mul_three_g)

    let sum_fact = triple_g_eq_sum_proof(d, p, a, b, c); // Equiv(mul_three_g, add a (add b c))
    let bc = cadd(d, p, b, c);
    let abc = cadd(d, p, a, bc);
    chain(
        d,
        p,
        g_gg,
        &[(mul_three_g, mul_to_g_gg_symm), (abc, sum_fact)],
    )
}

/// `Equiv (dot w zero_point) CReal.zero`, where `zero_point := CPoint.mk
/// CReal.zero CReal.zero`. Turns "the three vertex-to-centroid vectors sum to
/// the zero point" ([`triple_sub_sum_zero_proof`], packaged per coordinate)
/// into "every dot product against that sum is zero" — the cross-term
/// cancellation [`CPointPrelude::centroid_dist_sq`] needs.
fn dot_zero_right_proof(d: &mut IntDev<'_>, p: CPointPrelude, w: ExprId) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let zero_point = d.const_app(p.mk, &[zero, zero]);
    let dot_w_zp = dotp(d, p, w, zero_point);
    let wx = d.const_app(p.x, &[w]);
    let wy = d.const_app(p.y, &[w]);
    let mul_wx_zero = cmul(d, p, wx, zero);
    let mul_wy_zero = cmul(d, p, wy, zero);
    let raw = cadd(d, p, mul_wx_zero, mul_wy_zero); // =defeq= dot_w_zp

    let mz_x = d.lemma(creal.mul_zero, &[wx]); // Equiv(mul_wx_zero, zero)
    let mz_y = d.lemma(creal.mul_zero, &[wy]); // Equiv(mul_wy_zero, zero)
    let congr = d.lemma(
        creal.add_congr,
        &[mul_wx_zero, zero, mul_wy_zero, zero, mz_x, mz_y],
    ); // Equiv(raw, add zero zero)
    let zero_zero = cadd(d, p, zero, zero);
    let az = d.lemma(creal.add_zero, &[zero]); // Equiv(zero_zero, zero)

    let bridge = refl(d, p, raw);
    chain(
        d,
        p,
        dot_w_zp,
        &[(raw, bridge), (zero_zero, congr), (zero, az)],
    )
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

/// `Scalar.one_sub_inv2 : Equiv (add CReal.one (neg inv2)) inv2`. See
/// [`CPointPrelude::one_sub_inv2`].
fn declare_one_sub_inv2(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let two = d.kernel().const_(p.two, vec![]);
    let one = d.kernel().const_(creal.one, vec![]);
    let zero_nat = d.num(0);
    let h_two = d.kernel().const_(p.two_pos_bound, vec![]);

    // inv2 + inv2 ~ mul two inv2 ~ one.
    let double_inv2 = two_mul_eq_double_proof(d, p, inv2); // Equiv(mul two inv2, add inv2 inv2)
    let mul_two_inv2 = cmul(d, p, two, inv2);
    let inv2_inv2 = cadd(d, p, inv2, inv2);
    let cancel = d.lemma(creal.mul_inv_cancel, &[two, zero_nat, h_two]); // Equiv(mul_two_inv2, one)
    let inv2_inv2_symm = symm(d, p, mul_two_inv2, inv2_inv2, double_inv2); // Equiv(inv2_inv2, mul_two_inv2)
    let h_ii = chain(
        d,
        p,
        inv2_inv2,
        &[(mul_two_inv2, inv2_inv2_symm), (one, cancel)],
    ); // Equiv(inv2_inv2, one)

    // (inv2+inv2) - inv2 ~ inv2.
    let cancel_step = add_sub_cancel_left(d, p, inv2, inv2); // Equiv(add inv2_inv2 (neg inv2), inv2)

    let neg_inv2 = cneg(d, p, inv2);
    let one_neg_inv2 = cadd(d, p, one, neg_inv2);
    let ii_neg_inv2 = cadd(d, p, inv2_inv2, neg_inv2);
    let h_ii_symm = symm(d, p, inv2_inv2, one, h_ii); // Equiv(one, inv2_inv2)
    let refl_neg_inv2 = refl(d, p, neg_inv2);
    let congr = d.lemma(
        creal.add_congr,
        &[one, inv2_inv2, neg_inv2, neg_inv2, h_ii_symm, refl_neg_inv2],
    ); // Equiv(one_neg_inv2, ii_neg_inv2)

    let final_proof = chain(
        d,
        p,
        one_neg_inv2,
        &[(ii_neg_inv2, congr), (inv2, cancel_step)],
    );

    let ty = equiv(d, p, one_neg_inv2, inv2);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.one_sub_inv2,
        uparams: vec![],
        ty,
        value: final_proof,
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

/// `dot_self_add : ∀ U V, Equiv (dot (add U V) (add U V))
/// (add (dot U U) (add (dot U V) (add (dot U V) (dot V V))))`. See
/// [`CPointPrelude::dot_self_add`].
fn declare_dot_self_add(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let u_fv = d.fresh_fvar();
    let pu = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let pv = d.kernel().fvar(v_fv);

    let sum_uv = padd(d, p, pu, pv);
    let lhs = dotp(d, p, sum_uv, sum_uv);

    let uu = dotp(d, p, pu, pu);
    let uv = dotp(d, p, pu, pv);
    let vu = dotp(d, p, pv, pu);
    let vv = dotp(d, p, pv, pv);

    // Step 1: dot(U+V, U+V) ~ dot(U, U+V) + dot(V, U+V).
    let dot_u_sum = dotp(d, p, pu, sum_uv);
    let dot_v_sum = dotp(d, p, pv, sum_uv);
    let mid1 = cadd(d, p, dot_u_sum, dot_v_sum);
    let step1 = d.lemma(p.dot_add_left, &[pu, pv, sum_uv]); // Equiv(lhs, mid1)

    // Step 2: split each summand via dot_add_right.
    let step2a = d.lemma(p.dot_add_right, &[pu, pu, pv]); // Equiv(dot_u_sum, add uu uv)
    let step2b = d.lemma(p.dot_add_right, &[pv, pu, pv]); // Equiv(dot_v_sum, add vu vv)
    let uu_uv = cadd(d, p, uu, uv);
    let vu_vv = cadd(d, p, vu, vv);
    let combined2 = d.lemma(
        creal.add_congr,
        &[dot_u_sum, uu_uv, dot_v_sum, vu_vv, step2a, step2b],
    ); // Equiv(mid1, add uu_uv vu_vv)
    let expr2 = cadd(d, p, uu_uv, vu_vv);

    // Step 3: fold `dot V U` back into `dot U V` via dot_comm.
    let comm_vu = d.lemma(p.dot_comm, &[pv, pu]); // Equiv(vu, uv)
    let uv_vv = cadd(d, p, uv, vv);
    let refl_vv = refl(d, p, vv);
    let congr_inner = d.lemma(creal.add_congr, &[vu, uv, vv, vv, comm_vu, refl_vv]); // Equiv(vu_vv, uv_vv)
    let refl_uuuv = refl(d, p, uu_uv);
    let combined3 = d.lemma(
        creal.add_congr,
        &[uu_uv, uu_uv, vu_vv, uv_vv, refl_uuuv, congr_inner],
    ); // Equiv(expr2, add uu_uv uv_vv)
    let expr3 = cadd(d, p, uu_uv, uv_vv);

    // Step 4: regroup into the right-nested target via add_assoc.
    let assoc = d.lemma(creal.add_assoc, &[uu, uv, uv_vv]); // Equiv(expr3, add uu (add uv uv_vv))
    let uv_uv_vv = cadd(d, p, uv, uv_vv);
    let target = cadd(d, p, uu, uv_uv_vv);

    let proof = chain(
        d,
        p,
        lhs,
        &[
            (mid1, step1),
            (expr2, combined2),
            (expr3, combined3),
            (target, assoc),
        ],
    );

    let ty_body = equiv(d, p, lhs, target);
    let ty = {
        let inner = d.pi_fv(v_fv, point, ty_body);
        d.pi_fv(u_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(v_fv, point, proof);
        d.lam_fv(u_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_self_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dot_self_sub : ∀ U V, Equiv (dot (sub U V) (sub U V))
/// (add (dot U U) (add (neg (dot U V)) (add (neg (dot U V)) (dot V V))))`.
/// See [`CPointPrelude::dot_self_sub`].
fn declare_dot_self_sub(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let u_fv = d.fresh_fvar();
    let pu = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let pv = d.kernel().fvar(v_fv);

    let sub_uv = psub(d, p, pu, pv);
    let lhs = dotp(d, p, sub_uv, sub_uv);

    let uu = dotp(d, p, pu, pu);
    let uv = dotp(d, p, pu, pv);
    let vu = dotp(d, p, pv, pu);
    let vv = dotp(d, p, pv, pv);
    let neg_uv = cneg(d, p, uv);
    let neg_vv = cneg(d, p, vv);

    // Step 1: dot(U-V, U-V) ~ dot(U, U-V) + neg(dot(V, U-V)).
    let dot_u_subuv = dotp(d, p, pu, sub_uv);
    let dot_v_subuv = dotp(d, p, pv, sub_uv);
    let neg_dot_v_subuv = cneg(d, p, dot_v_subuv);
    let mid1 = cadd(d, p, dot_u_subuv, neg_dot_v_subuv);
    let step1 = d.lemma(p.dot_sub_left, &[pu, pv, sub_uv]); // Equiv(lhs, mid1)

    // Step 2: split each summand via dot_sub_right.
    let step2a = d.lemma(p.dot_sub_right, &[pu, pu, pv]); // Equiv(dot_u_subuv, add uu (neg uv))
    let step2b = d.lemma(p.dot_sub_right, &[pv, pu, pv]); // Equiv(dot_v_subuv, add vu (neg vv))
    let uu_neguv = cadd(d, p, uu, neg_uv);
    let vu_negvv = cadd(d, p, vu, neg_vv);
    let neg_vu_negvv = cneg(d, p, vu_negvv);
    let neg_congr_2b = d.lemma(creal.neg_congr, &[dot_v_subuv, vu_negvv, step2b]); // Equiv(neg_dot_v_subuv, neg_vu_negvv)
    let combined2 = d.lemma(
        creal.add_congr,
        &[
            dot_u_subuv,
            uu_neguv,
            neg_dot_v_subuv,
            neg_vu_negvv,
            step2a,
            neg_congr_2b,
        ],
    ); // Equiv(mid1, add uu_neguv neg_vu_negvv)
    let expr2 = cadd(d, p, uu_neguv, neg_vu_negvv);

    // Step 3: simplify neg(add vu (neg vv)) ~ add (neg vu) vv.
    let neg_vu = cneg(d, p, vu);
    let neg_neg_vv = cneg(d, p, neg_vv);
    let na = neg_add_proof(d, p, vu, neg_vv); // Equiv(neg_vu_negvv, add neg_vu neg_neg_vv)
    let nn = neg_neg_proof(d, p, vv); // Equiv(neg_neg_vv, vv)
    let refl_negvu = refl(d, p, neg_vu);
    let congr_nn = d.lemma(
        creal.add_congr,
        &[neg_vu, neg_vu, neg_neg_vv, vv, refl_negvu, nn],
    ); // Equiv(add neg_vu neg_neg_vv, add neg_vu vv)
    let neg_vu_negnegvv = cadd(d, p, neg_vu, neg_neg_vv);
    let neg_vu_vv = cadd(d, p, neg_vu, vv);
    let simp1 = chain(
        d,
        p,
        neg_vu_negvv,
        &[(neg_vu_negnegvv, na), (neg_vu_vv, congr_nn)],
    ); // Equiv(neg_vu_negvv, neg_vu_vv)

    let refl_uuneguv = refl(d, p, uu_neguv);
    let combined3 = d.lemma(
        creal.add_congr,
        &[
            uu_neguv,
            uu_neguv,
            neg_vu_negvv,
            neg_vu_vv,
            refl_uuneguv,
            simp1,
        ],
    ); // Equiv(expr2, add uu_neguv neg_vu_vv)
    let expr3 = cadd(d, p, uu_neguv, neg_vu_vv);

    // Step 4: fold `neg (dot V U)` back into `neg (dot U V)` via dot_comm.
    let comm_vu = d.lemma(p.dot_comm, &[pv, pu]); // Equiv(vu, uv)
    let neg_congr_vu = d.lemma(creal.neg_congr, &[vu, uv, comm_vu]); // Equiv(neg_vu, neg_uv)
    let refl_vv2 = refl(d, p, vv);
    let congr4 = d.lemma(
        creal.add_congr,
        &[neg_vu, neg_uv, vv, vv, neg_congr_vu, refl_vv2],
    ); // Equiv(neg_vu_vv, add neg_uv vv)
    let neg_uv_vv = cadd(d, p, neg_uv, vv);
    let combined4 = d.lemma(
        creal.add_congr,
        &[
            uu_neguv,
            uu_neguv,
            neg_vu_vv,
            neg_uv_vv,
            refl_uuneguv,
            congr4,
        ],
    ); // Equiv(expr3, add uu_neguv neg_uv_vv)
    let expr4 = cadd(d, p, uu_neguv, neg_uv_vv);

    // Step 5: regroup into the right-nested target via add_assoc.
    let assoc = d.lemma(creal.add_assoc, &[uu, neg_uv, neg_uv_vv]); // Equiv(expr4, add uu (add neg_uv neg_uv_vv))
    let neg_uv_neg_uv_vv = cadd(d, p, neg_uv, neg_uv_vv);
    let target = cadd(d, p, uu, neg_uv_neg_uv_vv);

    let proof = chain(
        d,
        p,
        lhs,
        &[
            (mid1, step1),
            (expr2, combined2),
            (expr3, combined3),
            (expr4, combined4),
            (target, assoc),
        ],
    );

    let ty_body = equiv(d, p, lhs, target);
    let ty = {
        let inner = d.pi_fv(v_fv, point, ty_body);
        d.pi_fv(u_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(v_fv, point, proof);
        d.lam_fv(u_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_self_sub,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dot_self_add3 : ∀ U V W,
/// Equiv (dot (add (add U V) W) (add (add U V) W))
///       (add (add (dot U U) (add (dot U V) (add (dot U V) (dot V V))))
///            (add (add (dot U W) (dot V W))
///                 (add (add (dot U W) (dot V W)) (dot W W))))`.
/// See [`CPointPrelude::dot_self_add3`].
fn declare_dot_self_add3(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let u_fv = d.fresh_fvar();
    let pu = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let pv = d.kernel().fvar(v_fv);
    let w_fv = d.fresh_fvar();
    let pw = d.kernel().fvar(w_fv);

    let sum_uv = padd(d, p, pu, pv);
    let sum_uvw = padd(d, p, sum_uv, pw);
    let lhs = dotp(d, p, sum_uvw, sum_uvw);

    // Step 1: expand via dot_self_add at (U+V, W).
    //   Equiv(lhs, add a1 (add b1 (add b1 c1)))
    // where a1 = dot(U+V,U+V), b1 = dot(U+V,W), c1 = dot(W,W).
    let a1 = dotp(d, p, sum_uv, sum_uv);
    let b1 = dotp(d, p, sum_uv, pw);
    let c1 = dotp(d, p, pw, pw);
    let step1 = d.lemma(p.dot_self_add, &[sum_uv, pw]); // Equiv(lhs, mid1)
    let b1_c1 = cadd(d, p, b1, c1);
    let b1_b1c1 = cadd(d, p, b1, b1_c1);
    let mid1 = cadd(d, p, a1, b1_b1c1);

    // Step 2: expand a1 via dot_self_add at (U, V).
    let uu = dotp(d, p, pu, pu);
    let uv = dotp(d, p, pu, pv);
    let vv = dotp(d, p, pv, pv);
    let step_a1 = d.lemma(p.dot_self_add, &[pu, pv]); // Equiv(a1, a1p)
    let uv_vv = cadd(d, p, uv, vv);
    let uv_uvvv = cadd(d, p, uv, uv_vv);
    let a1p = cadd(d, p, uu, uv_uvvv);

    // Step 3: expand b1 (both occurrences) via dot_add_left at (U, V, W).
    let uw = dotp(d, p, pu, pw);
    let vw = dotp(d, p, pv, pw);
    let step_b1 = d.lemma(p.dot_add_left, &[pu, pv, pw]); // Equiv(b1, b1p)
    let b1p = cadd(d, p, uw, vw);

    // Combine: mid1 ~ a1p + (b1p + (b1p + c1)).
    let refl_c1 = refl(d, p, c1);
    let congr_inner1 = d.lemma(creal.add_congr, &[b1, b1p, c1, c1, step_b1, refl_c1]); // Equiv(b1_c1, b1p+c1)
    let b1p_c1 = cadd(d, p, b1p, c1);
    let congr_inner2 = d.lemma(
        creal.add_congr,
        &[b1, b1p, b1_c1, b1p_c1, step_b1, congr_inner1],
    ); // Equiv(b1_b1c1, b1p+(b1p+c1))
    let b1p_b1pc1 = cadd(d, p, b1p, b1p_c1);
    let congr_outer = d.lemma(
        creal.add_congr,
        &[a1, a1p, b1_b1c1, b1p_b1pc1, step_a1, congr_inner2],
    ); // Equiv(mid1, a1p+b1p_b1pc1)
    let target = cadd(d, p, a1p, b1p_b1pc1);

    let proof = chain(d, p, lhs, &[(mid1, step1), (target, congr_outer)]);

    let ty_body = equiv(d, p, lhs, target);
    let ty = {
        let inner2 = d.pi_fv(w_fv, point, ty_body);
        let inner1 = d.pi_fv(v_fv, point, inner2);
        d.pi_fv(u_fv, point, inner1)
    };
    let value = {
        let inner2 = d.lam_fv(w_fv, point, proof);
        let inner1 = d.lam_fv(v_fv, point, inner2);
        d.lam_fv(u_fv, point, inner1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_self_add3,
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

// --- orthocentre identity: generic scalar/point combinators ----------------

/// `CPoint.Equiv (sub pt m) (neg (sub m pt))`, generic over the raw
/// coordinates of `m` and `pt` — the "`P - A ~ neg (A - P)`" shape consumed
/// three times in [`declare_orthocentre_identity`] (for `A`, `B`, `C` in turn
/// as `m`, always against the shared vertex `pt` as `P`). Per-coordinate
/// `symm` of `neg_sub_comm_scalar_proof`, packaged via [`and_intro`] the
/// same way [`declare_pythagoras`] packages `diff_diff_scalar_proof`.
fn point_sub_eq_neg_sub_fact(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    mx: ExprId,
    my: ExprId,
    ptx: ExprId,
    pty: ExprId,
) -> ExprId {
    let neg_mx = cneg(d, p, mx);
    let raw_lhs_x = cadd(d, p, ptx, neg_mx);
    let neg_ptx = cneg(d, p, ptx);
    let mx_neg_ptx = cadd(d, p, mx, neg_ptx);
    let raw_rhs_x = cneg(d, p, mx_neg_ptx);
    let claim_x = equiv(d, p, raw_lhs_x, raw_rhs_x);
    let proof_x = {
        let inner = neg_sub_comm_scalar_proof(d, p, mx, ptx); // Equiv(raw_rhs_x, raw_lhs_x)
        symm(d, p, raw_rhs_x, raw_lhs_x, inner)
    };
    let neg_my = cneg(d, p, my);
    let raw_lhs_y = cadd(d, p, pty, neg_my);
    let neg_pty = cneg(d, p, pty);
    let my_neg_pty = cadd(d, p, my, neg_pty);
    let raw_rhs_y = cneg(d, p, my_neg_pty);
    let claim_y = equiv(d, p, raw_lhs_y, raw_rhs_y);
    let proof_y = {
        let inner = neg_sub_comm_scalar_proof(d, p, my, pty);
        symm(d, p, raw_rhs_y, raw_lhs_y, inner)
    };
    and_intro(d, p, claim_x, claim_y, proof_x, proof_y)
}

/// `CPoint.Equiv (sub a b) (sub (sub a c) (sub b c))`, generic over the raw
/// coordinates of `a`, `b`, `c` — the "`A - B ~ (A-P) - (B-P)`" shape consumed
/// three times in [`declare_orthocentre_identity`]. Per-coordinate
/// `diff_diff_scalar_proof`, packaged via [`and_intro`] exactly the way
/// [`declare_pythagoras`]'s `diff_ab_w` is.
fn point_diff_diff_fact(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    ax: ExprId,
    ay: ExprId,
    bx: ExprId,
    by: ExprId,
    cx: ExprId,
    cy: ExprId,
) -> ExprId {
    let diff_x = diff_diff_scalar_proof(d, p, ax, bx, cx);
    let diff_y = diff_diff_scalar_proof(d, p, ay, by, cy);
    let neg_bx = cneg(d, p, bx);
    let raw_lhs_x = cadd(d, p, ax, neg_bx);
    let n_cx = cneg(d, p, cx);
    let ac_x = cadd(d, p, ax, n_cx);
    let bc_x = cadd(d, p, bx, n_cx);
    let neg_bc_x = cneg(d, p, bc_x);
    let raw_rhs_x = cadd(d, p, ac_x, neg_bc_x);
    let claim_x = equiv(d, p, raw_lhs_x, raw_rhs_x);
    let neg_by = cneg(d, p, by);
    let raw_lhs_y = cadd(d, p, ay, neg_by);
    let n_cy = cneg(d, p, cy);
    let ac_y = cadd(d, p, ay, n_cy);
    let bc_y = cadd(d, p, by, n_cy);
    let neg_bc_y = cneg(d, p, bc_y);
    let raw_rhs_y = cadd(d, p, ac_y, neg_bc_y);
    let claim_y = equiv(d, p, raw_lhs_y, raw_rhs_y);
    and_intro(d, p, claim_x, claim_y, diff_x, diff_y)
}

/// `Equiv (dot (neg u) (sub c e)) (add (neg (dot u c)) (dot u e))`.
///
/// `dot_neg_left` peels the outer `neg`, `dot_sub_right` splits the `sub`,
/// then `neg_add_proof`/`neg_neg_proof` push the resulting `neg` back inward
/// — exactly the "simplify a double negation" block
/// [`declare_pythagoras`] uses for its own `dot_sub_left`/`dot_sub_right`
/// combination, specialised to a `neg` on the left slot instead of a `sub`.
/// Returns `(rhs, proof)`.
fn expand_dot_neg_sub(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    big_u: ExprId,
    c: ExprId,
    e: ExprId,
) -> (ExprId, ExprId) {
    let creal = p.creal;
    let neg_u = pneg(d, p, big_u);
    let sub_ce = psub(d, p, c, e);
    let lhs = dotp(d, p, neg_u, sub_ce);
    let dot_u_ce = dotp(d, p, big_u, sub_ce);
    let neg_dot_u_ce = cneg(d, p, dot_u_ce);
    let dnl = d.lemma(p.dot_neg_left, &[big_u, sub_ce]); // Equiv(lhs, neg_dot_u_ce)

    let dot_uc = dotp(d, p, big_u, c);
    let dot_ue = dotp(d, p, big_u, e);
    let neg_dot_ue = cneg(d, p, dot_ue);
    let mid = cadd(d, p, dot_uc, neg_dot_ue);
    let dsr = d.lemma(p.dot_sub_right, &[big_u, c, e]); // Equiv(dot_u_ce, mid)

    let neg_mid = cneg(d, p, mid);
    let na = neg_add_proof(d, p, dot_uc, neg_dot_ue); // Equiv(neg_mid, add(neg dot_uc)(neg neg_dot_ue))
    let nn = neg_neg_proof(d, p, dot_ue); // Equiv(neg neg_dot_ue, dot_ue)
    let neg_dot_uc = cneg(d, p, dot_uc);
    let neg_neg_dot_ue = cneg(d, p, neg_dot_ue);
    let refl_neg_uc = refl(d, p, neg_dot_uc);
    let congr_nn = d.lemma(
        creal.add_congr,
        &[
            neg_dot_uc,
            neg_dot_uc,
            neg_neg_dot_ue,
            dot_ue,
            refl_neg_uc,
            nn,
        ],
    ); // Equiv(add neg_dot_uc neg_neg_dot_ue, add neg_dot_uc dot_ue)
    let na_target = cadd(d, p, neg_dot_uc, neg_neg_dot_ue);
    let rhs = cadd(d, p, neg_dot_uc, dot_ue);
    let simplify = chain(d, p, neg_mid, &[(na_target, na), (rhs, congr_nn)]);

    let neg_congr_dsr = d.lemma(creal.neg_congr, &[dot_u_ce, mid, dsr]); // Equiv(neg_dot_u_ce, neg_mid)
    let proof = chain(
        d,
        p,
        lhs,
        &[
            (neg_dot_u_ce, dnl),
            (neg_mid, neg_congr_dsr),
            (rhs, simplify),
        ],
    );
    (rhs, proof)
}

/// `Equiv (add x (neg y)) zero`, given `hxy : Equiv x y`.
fn cancel_pos_neg(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    hxy: ExprId,
) -> ExprId {
    let creal = p.creal;
    let hxy_symm = symm(d, p, x, y, hxy); // Equiv y x
    let neg_y = cneg(d, p, y);
    let neg_x = cneg(d, p, x);
    let ncongr = d.lemma(creal.neg_congr, &[y, x, hxy_symm]); // Equiv(neg y, neg x)
    let refl_x = refl(d, p, x);
    let combined = d.lemma(creal.add_congr, &[x, x, neg_y, neg_x, refl_x, ncongr]); // Equiv(add x neg_y, add x neg_x)
    let an = d.lemma(creal.add_neg, &[x]); // Equiv(add x neg_x, zero)
    let lhs = cadd(d, p, x, neg_y);
    let mid = cadd(d, p, x, neg_x);
    let zero = czero(d, p);
    chain(d, p, lhs, &[(mid, combined), (zero, an)])
}

/// `Equiv (add (neg x) y) zero`, given `hxy : Equiv x y`.
fn cancel_neg_pos(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    hxy: ExprId,
) -> ExprId {
    let creal = p.creal;
    let hxy_symm = symm(d, p, x, y, hxy); // Equiv y x
    let neg_x = cneg(d, p, x);
    let refl_negx = refl(d, p, neg_x);
    let combined = d.lemma(creal.add_congr, &[neg_x, neg_x, y, x, refl_negx, hxy_symm]); // Equiv(add neg_x y, add neg_x x)
    let nac = neg_add_cancel_proof(d, p, x); // Equiv(add neg_x x, zero)
    let lhs = cadd(d, p, neg_x, y);
    let mid = cadd(d, p, neg_x, x);
    let zero = czero(d, p);
    chain(d, p, lhs, &[(mid, combined), (zero, nac)])
}

/// `Equiv (add x (add (neg y) z)) z`, given `hxy : Equiv x y` — "an adjacent
/// `x` cancels against a `neg y` buried one level down, leaving `z`". The
/// three-fold reuse of this one lemma (via [`Self::dot_comm`] for `hxy`) is
/// what keeps [`declare_orthocentre_identity`]'s final assembly to a handful
/// of `add_assoc`/`add_congr` steps instead of a from-scratch 12-term
/// rearrangement.
fn reduce3(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    hxy: ExprId,
) -> ExprId {
    let creal = p.creal;
    let neg_y = cneg(d, p, y);
    let inner = cadd(d, p, neg_y, z);
    let lhs = cadd(d, p, x, inner);
    let x_negy = cadd(d, p, x, neg_y);
    let mid2 = cadd(d, p, x_negy, z);
    let assoc_proof = d.lemma(creal.add_assoc, &[x, neg_y, z]); // Equiv(mid2, lhs)
    let assoc_symm = symm(d, p, mid2, lhs, assoc_proof); // Equiv(lhs, mid2)

    let cpn = cancel_pos_neg(d, p, x, y, hxy); // Equiv(x_negy, zero)
    let zero = czero(d, p);
    let refl_z = refl(d, p, z);
    let congr1 = d.lemma(creal.add_congr, &[x_negy, zero, z, z, cpn, refl_z]); // Equiv(mid2, add zero z)
    let zero_z = cadd(d, p, zero, z);
    let za = zero_add_proof(d, p, z); // Equiv(zero_z, z)

    chain(d, p, lhs, &[(mid2, assoc_symm), (zero_z, congr1), (z, za)])
}

/// **The orthocentre identity, unconditional.** See
/// [`CPointPrelude::orthocentre_identity`].
fn declare_orthocentre_identity(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let p_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(p_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let px = d.const_app(p.x, &[pp]);
    let py = d.const_app(p.y, &[pp]);
    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);

    // u := A-P, v := B-P, w := C-P.
    let u = psub(d, p, pa, pp);
    let v = psub(d, p, pb, pp);
    let w = psub(d, p, pc, pp);
    let neg_u = pneg(d, p, u);
    let neg_v = pneg(d, p, v);
    let neg_w = pneg(d, p, w);
    let sub_wv = psub(d, p, w, v);
    let sub_uw = psub(d, p, u, w);
    let sub_vu = psub(d, p, v, u);

    let sub_pa = psub(d, p, pp, pa);
    let sub_cb = psub(d, p, pc, pb);
    let sub_pb = psub(d, p, pp, pb);
    let sub_ac = psub(d, p, pa, pc);
    let sub_pc = psub(d, p, pp, pc);
    let sub_ba = psub(d, p, pb, pa);

    let fact1 = point_sub_eq_neg_sub_fact(d, p, ax, ay, px, py); // sub_pa ~ neg_u
    let fact2 = point_diff_diff_fact(d, p, cx, cy, bx, by, px, py); // sub_cb ~ sub_wv
    let fact3 = point_sub_eq_neg_sub_fact(d, p, bx, by, px, py); // sub_pb ~ neg_v
    let fact4 = point_diff_diff_fact(d, p, ax, ay, cx, cy, px, py); // sub_ac ~ sub_uw
    let fact5 = point_sub_eq_neg_sub_fact(d, p, cx, cy, px, py); // sub_pc ~ neg_w
    let fact6 = point_diff_diff_fact(d, p, bx, by, ax, ay, px, py); // sub_ba ~ sub_vu

    let step1_a = d.lemma(p.dot_congr, &[sub_pa, neg_u, sub_cb, sub_wv, fact1, fact2]);
    let step1_b = d.lemma(p.dot_congr, &[sub_pb, neg_v, sub_ac, sub_uw, fact3, fact4]);
    let step1_c = d.lemma(p.dot_congr, &[sub_pc, neg_w, sub_ba, sub_vu, fact5, fact6]);

    let (rhs_a, exp_a) = expand_dot_neg_sub(d, p, u, w, v); // add(neg(dot u w), dot u v)
    let (rhs_b, exp_b) = expand_dot_neg_sub(d, p, v, u, w); // add(neg(dot v u), dot v w)
    let (rhs_c, exp_c) = expand_dot_neg_sub(d, p, w, v, u); // add(neg(dot w v), dot w u)

    let ta_raw = dotp(d, p, sub_pa, sub_cb);
    let tb_raw = dotp(d, p, sub_pb, sub_ac);
    let tc_raw = dotp(d, p, sub_pc, sub_ba);
    let dot_negu_wv = dotp(d, p, neg_u, sub_wv);
    let dot_negv_uw = dotp(d, p, neg_v, sub_uw);
    let dot_negw_vu = dotp(d, p, neg_w, sub_vu);

    let term_a_full = chain(d, p, ta_raw, &[(dot_negu_wv, step1_a), (rhs_a, exp_a)]);
    let term_b_full = chain(d, p, tb_raw, &[(dot_negv_uw, step1_b), (rhs_b, exp_b)]);
    let term_c_full = chain(d, p, tc_raw, &[(dot_negw_vu, step1_c), (rhs_c, exp_c)]);

    // The three raw-dot pairs the sum reduces to via `dot_comm`.
    let a1 = dotp(d, p, u, v);
    let a1p = dotp(d, p, v, u);
    let a2 = dotp(d, p, v, w);
    let a2p = dotp(d, p, w, v);
    let a3 = dotp(d, p, w, u);
    let a3p = dotp(d, p, u, w);

    let comm_uv = d.lemma(p.dot_comm, &[u, v]); // Equiv a1 a1p
    let comm_vw = d.lemma(p.dot_comm, &[v, w]); // Equiv a2 a2p
    let comm_uw = d.lemma(p.dot_comm, &[u, w]); // Equiv a3p a3

    let red1 = reduce3(d, p, a1, a1p, a2, comm_uv); // Equiv(add a1 rhs_b, a2)
    let red2 = reduce3(d, p, a2, a2p, a3, comm_vw); // Equiv(add a2 rhs_c, a3)
    let final_cancel = cancel_neg_pos(d, p, a3p, a3, comm_uw); // Equiv(add (neg a3p) a3, zero)

    let ta_tb_raw = cadd(d, p, ta_raw, tb_raw);
    let s0 = cadd(d, p, ta_tb_raw, tc_raw);

    let rhs_ab = cadd(d, p, rhs_a, rhs_b);
    let t1 = cadd(d, p, rhs_ab, rhs_c);
    let inner_congr = d.lemma(
        creal.add_congr,
        &[ta_raw, rhs_a, tb_raw, rhs_b, term_a_full, term_b_full],
    ); // Equiv(ta_tb_raw, rhs_ab)
    let p1 = d.lemma(
        creal.add_congr,
        &[ta_tb_raw, rhs_ab, tc_raw, rhs_c, inner_congr, term_c_full],
    ); // Equiv(s0, t1)

    let neg_a3p = cneg(d, p, a3p);
    let mid_ab = cadd(d, p, neg_a3p, a2);
    let a1_rhsb = cadd(d, p, a1, rhs_b);
    let assoc1_target = cadd(d, p, neg_a3p, a1_rhsb);
    let assoc1 = d.lemma(creal.add_assoc, &[neg_a3p, a1, rhs_b]); // Equiv(rhs_ab, assoc1_target)
    let refl_neg_a3p = refl(d, p, neg_a3p);
    let congr_red1 = d.lemma(
        creal.add_congr,
        &[neg_a3p, neg_a3p, a1_rhsb, a2, refl_neg_a3p, red1],
    ); // Equiv(assoc1_target, mid_ab)
    let x1_step = chain(
        d,
        p,
        rhs_ab,
        &[(assoc1_target, assoc1), (mid_ab, congr_red1)],
    );

    let t2 = cadd(d, p, mid_ab, rhs_c);
    let refl_rhsc = refl(d, p, rhs_c);
    let p2 = d.lemma(
        creal.add_congr,
        &[rhs_ab, mid_ab, rhs_c, rhs_c, x1_step, refl_rhsc],
    ); // Equiv(t1, t2)

    let a2_rhsc = cadd(d, p, a2, rhs_c);
    let assoc2_target = cadd(d, p, neg_a3p, a2_rhsc);
    let assoc2 = d.lemma(creal.add_assoc, &[neg_a3p, a2, rhs_c]); // Equiv(t2, assoc2_target)
    let refl_neg_a3p2 = refl(d, p, neg_a3p);
    let mid_abc = cadd(d, p, neg_a3p, a3);
    let congr_red2 = d.lemma(
        creal.add_congr,
        &[neg_a3p, neg_a3p, a2_rhsc, a3, refl_neg_a3p2, red2],
    ); // Equiv(assoc2_target, mid_abc)

    let zero = czero(d, p);
    let final_proof = chain(
        d,
        p,
        s0,
        &[
            (t1, p1),
            (t2, p2),
            (assoc2_target, assoc2),
            (mid_abc, congr_red2),
            (zero, final_cancel),
        ],
    );

    let ty_body = equiv(d, p, s0, zero);
    let ty = {
        let w4 = d.pi_fv(c_fv, point, ty_body);
        let w3 = d.pi_fv(b_fv, point, w4);
        let w2 = d.pi_fv(a_fv, point, w3);
        d.pi_fv(p_fv, point, w2)
    };
    let value = {
        let w4 = d.lam_fv(c_fv, point, final_proof);
        let w3 = d.lam_fv(b_fv, point, w4);
        let w2 = d.lam_fv(a_fv, point, w3);
        d.lam_fv(p_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.orthocentre_identity,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Concurrence of the altitudes.** See
/// [`CPointPrelude::orthocentre_third_altitude`].
fn declare_orthocentre_third_altitude(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let p_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(p_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let sub_pa = psub(d, p, pp, pa);
    let sub_cb = psub(d, p, pc, pb);
    let sub_pb = psub(d, p, pp, pb);
    let sub_ac = psub(d, p, pa, pc);
    let sub_pc = psub(d, p, pp, pc);
    let sub_ba = psub(d, p, pb, pa);

    let ta_raw = dotp(d, p, sub_pa, sub_cb);
    let tb_raw = dotp(d, p, sub_pb, sub_ac);
    let tc_raw = dotp(d, p, sub_pc, sub_ba);

    let zero = czero(d, p);
    let h1_ty = equiv(d, p, ta_raw, zero);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = equiv(d, p, tb_raw, zero);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let zz = d.lemma(creal.add_zero, &[zero]); // Equiv(add zero zero, zero)
    let c12 = d.lemma(creal.add_congr, &[ta_raw, zero, tb_raw, zero, h1, h2]); // Equiv(ta_tb_raw, zero_zero)
    let ta_tb_raw = cadd(d, p, ta_raw, tb_raw);
    let zero_zero = cadd(d, p, zero, zero);
    let c12_reduced = chain(d, p, ta_tb_raw, &[(zero_zero, c12), (zero, zz)]); // Equiv(ta_tb_raw, zero)

    let refl_tc = refl(d, p, tc_raw);
    let s0 = cadd(d, p, ta_tb_raw, tc_raw);
    let c3 = d.lemma(
        creal.add_congr,
        &[ta_tb_raw, zero, tc_raw, tc_raw, c12_reduced, refl_tc],
    ); // Equiv(s0, zero_tc)
    let zero_tc = cadd(d, p, zero, tc_raw);
    let za = zero_add_proof(d, p, tc_raw); // Equiv(zero_tc, tc_raw)
    let reduced = chain(d, p, s0, &[(zero_tc, c3), (tc_raw, za)]); // Equiv(s0, tc_raw)
    let reduced_symm = symm(d, p, s0, tc_raw, reduced); // Equiv(tc_raw, s0)

    let orth_inst = d.lemma(p.orthocentre_identity, &[pp, pa, pb, pc]); // Equiv(s0, zero)

    let final_proof = chain(d, p, tc_raw, &[(s0, reduced_symm), (zero, orth_inst)]);

    let concl = equiv(d, p, tc_raw, zero);
    let ty_body = {
        let inner = d.arrow(h2_ty, concl);
        d.arrow(h1_ty, inner)
    };
    let ty = {
        let w4 = d.pi_fv(c_fv, point, ty_body);
        let w3 = d.pi_fv(b_fv, point, w4);
        let w2 = d.pi_fv(a_fv, point, w3);
        d.pi_fv(p_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h2_fv, h2_ty, final_proof);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, inner);
        let w4 = d.lam_fv(c_fv, point, with_h1);
        let w3 = d.lam_fv(b_fv, point, w4);
        let w2 = d.lam_fv(a_fv, point, w3);
        d.lam_fv(p_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.orthocentre_third_altitude,
        uparams: vec![],
        ty,
        value,
    })
}

// --- distSq: squared Euclidean distance -------------------------------------

/// `CPoint.distSq P Q := CPoint.dot (CPoint.sub P Q) (CPoint.sub P Q)`.
fn declare_dist_sq(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let sub_ab = psub(d, p, pa, pb);
    let value_body = dotp(d, p, sub_ab, sub_ab);

    let value = {
        let inner = d.lam_fv(pb_fv, point, value_body);
        d.lam_fv(pa_fv, point, inner)
    };
    let ty = {
        let carrier = creal_ty(d, p);
        let inner = d.arrow(point, carrier);
        d.arrow(point, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.dist_sq,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 8),
    })
}

/// `Equiv (sub pa qa) (sub pb qb)`, given `hp : CPoint.Equiv pa pb` and
/// `hq : CPoint.Equiv qa qb` — the setoid obligation [`CPointPrelude::point_sub`]
/// needs before it can be rewritten under, built the same way
/// [`declare_dot_congr`] builds `dot`'s.
fn psub_congr_fact(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    pa: ExprId,
    pb: ExprId,
    qa: ExprId,
    qb: ExprId,
    hp: ExprId,
    hq: ExprId,
) -> ExprId {
    let creal = p.creal;
    let pax = d.const_app(p.x, &[pa]);
    let pay = d.const_app(p.y, &[pa]);
    let pbx = d.const_app(p.x, &[pb]);
    let pby = d.const_app(p.y, &[pb]);
    let qax = d.const_app(p.x, &[qa]);
    let qay = d.const_app(p.y, &[qa]);
    let qbx = d.const_app(p.x, &[qb]);
    let qby = d.const_app(p.y, &[qb]);

    let ex_ty = equiv(d, p, pax, pbx);
    let ey_ty = equiv(d, p, pay, pby);
    let hpx = d.and_left(ex_ty, ey_ty, hp);
    let hpy = d.and_right(ex_ty, ey_ty, hp);
    let fx_ty = equiv(d, p, qax, qbx);
    let fy_ty = equiv(d, p, qay, qby);
    let hqx = d.and_left(fx_ty, fy_ty, hq);
    let hqy = d.and_right(fx_ty, fy_ty, hq);

    let neg_qax = cneg(d, p, qax);
    let neg_qbx = cneg(d, p, qbx);
    let neg_congr_x = d.lemma(creal.neg_congr, &[qax, qbx, hqx]); // Equiv(neg_qax, neg_qbx)
    let proof_x = d.lemma(
        creal.add_congr,
        &[pax, pbx, neg_qax, neg_qbx, hpx, neg_congr_x],
    );

    let neg_qay = cneg(d, p, qay);
    let neg_qby = cneg(d, p, qby);
    let neg_congr_y = d.lemma(creal.neg_congr, &[qay, qby, hqy]);
    let proof_y = d.lemma(
        creal.add_congr,
        &[pay, pby, neg_qay, neg_qby, hpy, neg_congr_y],
    );

    let claim_x_lhs = cadd(d, p, pax, neg_qax);
    let claim_x_rhs = cadd(d, p, pbx, neg_qbx);
    let claim_y_lhs = cadd(d, p, pay, neg_qay);
    let claim_y_rhs = cadd(d, p, pby, neg_qby);
    let claim_x = equiv(d, p, claim_x_lhs, claim_x_rhs);
    let claim_y = equiv(d, p, claim_y_lhs, claim_y_rhs);
    and_intro(d, p, claim_x, claim_y, proof_x, proof_y)
}

/// `distSq_congr : ∀ P P' Q Q', CPoint.Equiv P P' → CPoint.Equiv Q Q' →
/// Equiv (distSq P Q) (distSq P' Q')`.
fn declare_dist_sq_congr(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);
    let qa_fv = d.fresh_fvar();
    let qa = d.kernel().fvar(qa_fv);
    let qb_fv = d.fresh_fvar();
    let qb = d.kernel().fvar(qb_fv);

    let hp_ty = d.const_app(p.point_equiv, &[pa, pb]);
    let hq_ty = d.const_app(p.point_equiv, &[qa, qb]);
    let hp_fv = d.fresh_fvar();
    let hp = d.kernel().fvar(hp_fv);
    let hq_fv = d.fresh_fvar();
    let hq = d.kernel().fvar(hq_fv);

    let sub_fact = psub_congr_fact(d, p, pa, pb, qa, qb, hp, hq); // Equiv(sub pa qa, sub pb qb)
    let sub_paqa = psub(d, p, pa, qa);
    let sub_pbqb = psub(d, p, pb, qb);
    let proof = d.lemma(
        p.dot_congr,
        &[sub_paqa, sub_pbqb, sub_paqa, sub_pbqb, sub_fact, sub_fact],
    );

    let dsq1 = d.const_app(p.dist_sq, &[pa, qa]);
    let dsq2 = d.const_app(p.dist_sq, &[pb, qb]);
    let ty_body = {
        let concl = equiv(d, p, dsq1, dsq2);
        let inner = d.arrow(hq_ty, concl);
        d.arrow(hp_ty, inner)
    };
    let ty = {
        let w4 = d.pi_fv(qb_fv, point, ty_body);
        let w3 = d.pi_fv(qa_fv, point, w4);
        let w2 = d.pi_fv(pb_fv, point, w3);
        d.pi_fv(pa_fv, point, w2)
    };
    let value = {
        let with_hq = d.lam_fv(hq_fv, hq_ty, proof);
        let with_hp = d.lam_fv(hp_fv, hp_ty, with_hq);
        let w4 = d.lam_fv(qb_fv, point, with_hp);
        let w3 = d.lam_fv(qa_fv, point, w4);
        let w2 = d.lam_fv(pb_fv, point, w3);
        d.lam_fv(pa_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dist_sq_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `distSq_comm : ∀ P Q, Equiv (distSq P Q) (distSq Q P)`.
///
/// `sub Q P ~ neg (sub P Q)` ([`point_sub_eq_neg_sub_fact`]), so `dot(sub Q P,
/// sub Q P) ~ dot(neg sub_PQ, neg sub_PQ) ~ dot(sub_PQ, sub_PQ)`
/// ([`dot_neg_neg_proof`]) — no coordinate arithmetic beyond what those two
/// already-proved facts supply.
fn declare_dist_sq_comm(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let pax = d.const_app(p.x, &[pa]);
    let pay = d.const_app(p.y, &[pa]);
    let pbx = d.const_app(p.x, &[pb]);
    let pby = d.const_app(p.y, &[pb]);

    let sub_ab = psub(d, p, pa, pb);
    let sub_ba = psub(d, p, pb, pa);
    let neg_sub_ab = pneg(d, p, sub_ab);

    // fact : CPoint.Equiv (sub pb pa) (neg (sub pa pb))
    let fact = point_sub_eq_neg_sub_fact(d, p, pax, pay, pbx, pby);

    let step1 = d.lemma(
        p.dot_congr,
        &[sub_ba, neg_sub_ab, sub_ba, neg_sub_ab, fact, fact],
    ); // Equiv(dot(sub_ba,sub_ba), dot(neg_sub_ab,neg_sub_ab))
    let step2 = dot_neg_neg_proof(d, p, sub_ab); // Equiv(dot(neg_sub_ab,neg_sub_ab), dot(sub_ab,sub_ab))

    let dot_baba = dotp(d, p, sub_ba, sub_ba);
    let dot_negneg = dotp(d, p, neg_sub_ab, neg_sub_ab);
    let dot_abab = dotp(d, p, sub_ab, sub_ab);
    let ba_to_ab = chain(d, p, dot_baba, &[(dot_negneg, step1), (dot_abab, step2)]); // Equiv(distSq B A, distSq A B)
    let proof = symm(d, p, dot_baba, dot_abab, ba_to_ab); // Equiv(distSq A B, distSq B A)

    let dsq_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dsq_ba = d.const_app(p.dist_sq, &[pb, pa]);
    let ty_body = equiv(d, p, dsq_ab, dsq_ba);
    let ty = {
        let inner = d.pi_fv(pb_fv, point, ty_body);
        d.pi_fv(pa_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(pb_fv, point, proof);
        d.lam_fv(pa_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dist_sq_comm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `distSq_self_zero : ∀ P, Equiv (distSq P P) CReal.zero`.
fn declare_dist_sq_self_zero(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);

    let neg_ax = cneg(d, p, ax);
    let vx = cadd(d, p, ax, neg_ax);
    let neg_ay = cneg(d, p, ay);
    let vy = cadd(d, p, ay, neg_ay);
    let zero = czero(d, p);

    let an_x = d.lemma(creal.add_neg, &[ax]); // Equiv(vx, zero)
    let an_y = d.lemma(creal.add_neg, &[ay]); // Equiv(vy, zero)

    let mul_vx_vx = cmul(d, p, vx, vx);
    let mul_vy_vy = cmul(d, p, vy, vy);
    let mul_zero_zero = cmul(d, p, zero, zero);
    let mz = d.lemma(creal.mul_zero, &[zero]); // Equiv(mul zero zero, zero)

    let congr_x = d.lemma(creal.mul_congr, &[vx, zero, vx, zero, an_x, an_x]);
    let mul_vx_vx_reduce = chain(d, p, mul_vx_vx, &[(mul_zero_zero, congr_x), (zero, mz)]);
    let congr_y = d.lemma(creal.mul_congr, &[vy, zero, vy, zero, an_y, an_y]);
    let mul_vy_vy_reduce = chain(d, p, mul_vy_vy, &[(mul_zero_zero, congr_y), (zero, mz)]);

    let sum = cadd(d, p, mul_vx_vx, mul_vy_vy); // == dot(sub pa pa, sub pa pa) == distSq pa pa
    let congr_sum = d.lemma(
        creal.add_congr,
        &[
            mul_vx_vx,
            zero,
            mul_vy_vy,
            zero,
            mul_vx_vx_reduce,
            mul_vy_vy_reduce,
        ],
    );
    let zero_zero = cadd(d, p, zero, zero);
    let az = d.lemma(creal.add_zero, &[zero]); // Equiv(add zero zero, zero)
    let proof = chain(d, p, sum, &[(zero_zero, congr_sum), (zero, az)]);

    let dsq = d.const_app(p.dist_sq, &[pa, pa]);
    let ty_body = equiv(d, p, dsq, zero);
    let ty = d.pi_fv(pa_fv, point, ty_body);
    let value = d.lam_fv(pa_fv, point, proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dist_sq_self_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (build_right_chain [x, neg x, y, neg y, z, neg z]) CReal.zero` —
/// three cancelling pairs, chained right-associatively. The reassociation
/// target [`declare_circumcentre_identity`] reaches via
/// [`reorder_right_chain`] after flattening its own (differently grouped)
/// statement.
fn six_term_cancel_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> ExprId {
    let creal = p.creal;
    let nx = cneg(d, p, x);
    let ny = cneg(d, p, y);
    let nz = cneg(d, p, z);
    let zero = czero(d, p);

    // Innermost: z + nz ~ zero.
    let l5 = d.lemma(creal.add_neg, &[z]);
    let z_nz = cadd(d, p, z, nz);

    // ny + (z+nz) ~ ny + zero ~ ny.
    let refl_ny = refl(d, p, ny);
    let c4 = d.lemma(creal.add_congr, &[ny, ny, z_nz, zero, refl_ny, l5]);
    let ny_zero = cadd(d, p, ny, zero);
    let az_ny = d.lemma(creal.add_zero, &[ny]);
    let ny_znz = cadd(d, p, ny, z_nz);
    let l4 = chain(d, p, ny_znz, &[(ny_zero, c4), (ny, az_ny)]);

    // y + (ny+(z+nz)) ~ y+ny ~ zero.
    let refl_y = refl(d, p, y);
    let c3 = d.lemma(creal.add_congr, &[y, y, ny_znz, ny, refl_y, l4]);
    let y_ny = cadd(d, p, y, ny);
    let an_y = d.lemma(creal.add_neg, &[y]);
    let y_nyznz = cadd(d, p, y, ny_znz);
    let l3 = chain(d, p, y_nyznz, &[(y_ny, c3), (zero, an_y)]);

    // nx + (y+(ny+(z+nz))) ~ nx+zero ~ nx.
    let refl_nx = refl(d, p, nx);
    let c2 = d.lemma(creal.add_congr, &[nx, nx, y_nyznz, zero, refl_nx, l3]);
    let nx_zero = cadd(d, p, nx, zero);
    let az_nx = d.lemma(creal.add_zero, &[nx]);
    let nx_ynyznz = cadd(d, p, nx, y_nyznz);
    let l2 = chain(d, p, nx_ynyznz, &[(nx_zero, c2), (nx, az_nx)]);

    // Outermost: x + (nx+(y+(ny+(z+nz)))) ~ x+nx ~ zero.
    let refl_x = refl(d, p, x);
    let c1 = d.lemma(creal.add_congr, &[x, x, nx_ynyznz, nx, refl_x, l2]);
    let x_nx = cadd(d, p, x, nx);
    let an_x = d.lemma(creal.add_neg, &[x]);
    let x_nxynyznz = cadd(d, p, x, nx_ynyznz);
    chain(d, p, x_nxynyznz, &[(x_nx, c1), (zero, an_x)])
}

/// **The circumcentre identity, unconditional.** See
/// [`CPointPrelude::circumcentre_identity`].
fn declare_circumcentre_identity(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let x_ = d.const_app(p.dist_sq, &[po, pa]);
    let y_ = d.const_app(p.dist_sq, &[po, pb]);
    let z_ = d.const_app(p.dist_sq, &[po, pc]);
    let nx = cneg(d, p, x_);
    let ny = cneg(d, p, y_);
    let nz = cneg(d, p, z_);

    // lhs_tree = ((x+ny)+(y+nz)) + (z+nx) = (ta+tb)+tc.
    let lhs_tree = sadd(
        sadd(
            sadd(SumTree::Leaf(x_), SumTree::Leaf(ny)),
            sadd(SumTree::Leaf(y_), SumTree::Leaf(nz)),
        ),
        sadd(SumTree::Leaf(z_), SumTree::Leaf(nx)),
    );
    let lhs = sum_tree_build(d, p, &lhs_tree);
    let (lhs_chain, lhs_flatten) = flatten_sum_tree(d, p, &lhs_tree); // Equiv(lhs, lhs_chain)

    let mut lhs_leaves = Vec::new();
    sum_tree_leaves(&lhs_tree, &mut lhs_leaves); // [x, ny, y, nz, z, nx]
    let to_leaves = vec![x_, nx, y_, ny, z_, nz];
    let reorder = reorder_right_chain(d, p, &lhs_leaves, &to_leaves); // Equiv(lhs_chain, to_chain)
    let to_chain = build_right_chain(d, p, &to_leaves);

    let cancel = six_term_cancel_proof(d, p, x_, y_, z_); // Equiv(to_chain, zero)
    let zero = czero(d, p);

    let final_proof = chain(
        d,
        p,
        lhs,
        &[
            (lhs_chain, lhs_flatten),
            (to_chain, reorder),
            (zero, cancel),
        ],
    );

    let ty_body = equiv(d, p, lhs, zero);
    let ty = {
        let w3 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w3);
        let w1 = d.pi_fv(a_fv, point, w2);
        d.pi_fv(o_fv, point, w1)
    };
    let value = {
        let w3 = d.lam_fv(c_fv, point, final_proof);
        let w2 = d.lam_fv(b_fv, point, w3);
        let w1 = d.lam_fv(a_fv, point, w2);
        d.lam_fv(o_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.circumcentre_identity,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Concurrence of the two circumcentre equalities.** See
/// [`CPointPrelude::circumcentre_third_distance`].
fn declare_circumcentre_third_distance(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let x_ = d.const_app(p.dist_sq, &[po, pa]);
    let y_ = d.const_app(p.dist_sq, &[po, pb]);
    let z_ = d.const_app(p.dist_sq, &[po, pc]);

    let h1_ty = equiv(d, p, x_, y_);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = equiv(d, p, y_, z_);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    // ta := x + neg y ~ 0, from h1; tb := y + neg z ~ 0, from h2.
    let ta = cancel_pos_neg(d, p, x_, y_, h1);
    let tb = cancel_pos_neg(d, p, y_, z_, h2);

    let neg_y = cneg(d, p, y_);
    let neg_z = cneg(d, p, z_);
    let neg_x = cneg(d, p, x_);
    let ta_raw = cadd(d, p, x_, neg_y);
    let tb_raw = cadd(d, p, y_, neg_z);
    let tc_raw = cadd(d, p, z_, neg_x);

    let zero = czero(d, p);
    let zz = d.lemma(creal.add_zero, &[zero]); // Equiv(add zero zero, zero)
    let c12 = d.lemma(creal.add_congr, &[ta_raw, zero, tb_raw, zero, ta, tb]);
    let ta_tb_raw = cadd(d, p, ta_raw, tb_raw);
    let zero_zero = cadd(d, p, zero, zero);
    let c12_reduced = chain(d, p, ta_tb_raw, &[(zero_zero, c12), (zero, zz)]); // Equiv(ta_tb_raw, zero)

    let refl_tc = refl(d, p, tc_raw);
    let s0 = cadd(d, p, ta_tb_raw, tc_raw);
    let c3 = d.lemma(
        creal.add_congr,
        &[ta_tb_raw, zero, tc_raw, tc_raw, c12_reduced, refl_tc],
    ); // Equiv(s0, zero_tc)
    let zero_tc = cadd(d, p, zero, tc_raw);
    let za = zero_add_proof(d, p, tc_raw); // Equiv(zero_tc, tc_raw)
    let reduced = chain(d, p, s0, &[(zero_tc, c3), (tc_raw, za)]); // Equiv(s0, tc_raw)
    let reduced_symm = symm(d, p, s0, tc_raw, reduced); // Equiv(tc_raw, s0)

    let ident_inst = d.lemma(p.circumcentre_identity, &[po, pa, pb, pc]); // Equiv(s0, zero)
    let tc_zero = chain(d, p, tc_raw, &[(s0, reduced_symm), (zero, ident_inst)]); // Equiv(tc_raw, zero)

    // tc_raw = z + neg x ~ zero  =>  z ~ x  =>  x ~ z.
    let x_negx = cadd(d, p, x_, neg_x);
    let an_x = d.lemma(creal.add_neg, &[x_]); // Equiv(x_negx, zero)
    let an_x_symm = symm(d, p, x_negx, zero, an_x); // Equiv(zero, x_negx)
    let combined = chain(d, p, tc_raw, &[(zero, tc_zero), (x_negx, an_x_symm)]); // Equiv(tc_raw, x_negx)
    let zx_eq = d.lemma(p.add_right_cancel, &[z_, x_, neg_x, combined]); // Equiv(z_, x_)
    let final_proof = symm(d, p, z_, x_, zx_eq); // Equiv(x_, z_)

    let concl = equiv(d, p, x_, z_);
    let ty_body = {
        let inner = d.arrow(h2_ty, concl);
        d.arrow(h1_ty, inner)
    };
    let ty = {
        let w3 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w3);
        let w1 = d.pi_fv(a_fv, point, w2);
        d.pi_fv(o_fv, point, w1)
    };
    let value = {
        let inner = d.lam_fv(h2_fv, h2_ty, final_proof);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, inner);
        let w3 = d.lam_fv(c_fv, point, with_h1);
        let w2 = d.lam_fv(b_fv, point, w3);
        let w1 = d.lam_fv(a_fv, point, w2);
        d.lam_fv(o_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.circumcentre_third_distance,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Elements I.47, restated over `distSq`.** See
/// [`CPointPrelude::pythagoras_dist_sq`]: the `value` here is
/// [`CPointPrelude::pythagoras`] itself, instantiated at the same three
/// points — the only thing that differs is the *declared type*, which the
/// kernel accepts because `distSq` unfolds to exactly the `dot (sub _ _)
/// (sub _ _)` shape [`declare_pythagoras`] already proved over.
fn declare_pythagoras_dist_sq(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let sub_ac = psub(d, p, pa, pc);
    let sub_bc = psub(d, p, pb, pc);
    let dot_ac_bc = dotp(d, p, sub_ac, sub_bc);
    let zero = czero(d, p);
    let hyp_ty = equiv(d, p, dot_ac_bc, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let dsq_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dsq_ac = d.const_app(p.dist_sq, &[pa, pc]);
    let dsq_bc = d.const_app(p.dist_sq, &[pb, pc]);

    let inst = d.lemma(p.pythagoras, &[pa, pb, pc]); // hyp_ty -> (raw pythagoras conclusion)
    let applied = d.apply(inst, &[h]);

    let ty_body = {
        let dsq_ac_bc = cadd(d, p, dsq_ac, dsq_bc);
        let concl = equiv(d, p, dsq_ab, dsq_ac_bc);
        d.arrow(hyp_ty, concl)
    };
    let ty = {
        let w3 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h_fv, hyp_ty, applied);
        let w3 = d.lam_fv(c_fv, point, inner);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pythagoras_dist_sq,
        uparams: vec![],
        ty,
        value,
    })
}

// --- parallelogram diagonals bisect ------------------------------------------

/// **Parallelogram diagonals bisect each other.** See
/// [`CPointPrelude::parallelogram_diagonals_bisect`].
fn declare_parallelogram_diagonals_bisect(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    // The fourth point ("D"); named `e_fv` so the local `d` (the `IntDev`
    // builder) is never shadowed, matching `declare_varignon`'s convention.
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

    let sub_ba = psub(d, p, pb, pa);
    let sub_cd = psub(d, p, pc, pd);
    let hyp_ty = d.const_app(p.point_equiv, &[sub_ba, sub_cd]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let ex_ty = {
        let neg_ax = cneg(d, p, ax);
        let lhs = cadd(d, p, bx, neg_ax);
        let neg_dx = cneg(d, p, dx);
        let rhs = cadd(d, p, cx, neg_dx);
        equiv(d, p, lhs, rhs)
    };
    let ey_ty = {
        let neg_ay = cneg(d, p, ay);
        let lhs = cadd(d, p, by, neg_ay);
        let neg_dy = cneg(d, p, dy);
        let rhs = cadd(d, p, cy, neg_dy);
        equiv(d, p, lhs, rhs)
    };
    let hx = d.and_left(ex_ty, ey_ty, h);
    let hy = d.and_right(ex_ty, ey_ty, h);

    let core_x = diag_bisect_midpoint_scalar_proof(d, p, ax, bx, cx, dx, hx);
    let core_y = diag_bisect_midpoint_scalar_proof(d, p, ay, by, cy, dy, hy);

    let mid_ac_x = midpoint(d, p, ax, cx);
    let mid_bd_x = midpoint(d, p, bx, dx);
    let claim_x = equiv(d, p, mid_ac_x, mid_bd_x);
    let mid_ac_y = midpoint(d, p, ay, cy);
    let mid_bd_y = midpoint(d, p, by, dy);
    let claim_y = equiv(d, p, mid_ac_y, mid_bd_y);
    let proof = and_intro(d, p, claim_x, claim_y, core_x, core_y);

    let pmac = d.const_app(p.point_midpoint, &[pa, pc]);
    let pmbd = d.const_app(p.point_midpoint, &[pb, pd]);
    let ty_body = {
        let concl = d.const_app(p.point_equiv, &[pmac, pmbd]);
        d.arrow(hyp_ty, concl)
    };
    let ty = {
        let w4 = d.pi_fv(e_fv, point, ty_body);
        let w3 = d.pi_fv(c_fv, point, w4);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h_fv, hyp_ty, proof);
        let w4 = d.lam_fv(e_fv, point, inner);
        let w3 = d.lam_fv(c_fv, point, w4);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.parallelogram_diagonals_bisect,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Opposite sides of a parallelogram are equal in length.** See
/// [`CPointPrelude::parallelogram_opposite_sides_eq`].
fn declare_parallelogram_opposite_sides_eq(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    // The fourth point ("D"); named `e_fv` so the local `d` (the `IntDev`
    // builder) is never shadowed, matching `declare_varignon`'s convention.
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

    let sub_ba = psub(d, p, pb, pa);
    let sub_cd = psub(d, p, pc, pd);
    let hyp_ty = d.const_app(p.point_equiv, &[sub_ba, sub_cd]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let ex_ty = {
        let neg_ax = cneg(d, p, ax);
        let lhs = cadd(d, p, bx, neg_ax);
        let neg_dx = cneg(d, p, dx);
        let rhs = cadd(d, p, cx, neg_dx);
        equiv(d, p, lhs, rhs)
    };
    let ey_ty = {
        let neg_ay = cneg(d, p, ay);
        let lhs = cadd(d, p, by, neg_ay);
        let neg_dy = cneg(d, p, dy);
        let rhs = cadd(d, p, cy, neg_dy);
        equiv(d, p, lhs, rhs)
    };
    let hx = d.and_left(ex_ty, ey_ty, h);
    let hy = d.and_right(ex_ty, ey_ty, h);

    // CD ~ -(AB), per coordinate.
    let hwx = opposite_side_neg_scalar_proof(d, p, ax, bx, cx, dx, hx);
    let hwy = opposite_side_neg_scalar_proof(d, p, ay, by, cy, dy, hy);

    // DA ~ -(BC), per coordinate, reusing the CD ~ -(AB) facts above.
    let hzx = diag_side_neg_scalar_proof(d, p, ax, bx, cx, dx, hwx);
    let hzy = diag_side_neg_scalar_proof(d, p, ay, by, cy, dy, hwy);

    let sub_ab = psub(d, p, pa, pb);
    let sub_bc = psub(d, p, pb, pc);
    let sub_da = psub(d, p, pd, pa);
    let neg_u = pneg(d, p, sub_ab);
    let neg_v = pneg(d, p, sub_bc);

    // fact_w_negu : CPoint.Equiv (sub C D) (neg (sub A B))
    let fact_w_negu = {
        let neg_bx = cneg(d, p, bx);
        let ux = cadd(d, p, ax, neg_bx);
        let neg_ux = cneg(d, p, ux);
        let neg_dx = cneg(d, p, dx);
        let wx = cadd(d, p, cx, neg_dx);
        let claim_x = equiv(d, p, wx, neg_ux);

        let neg_by = cneg(d, p, by);
        let uy = cadd(d, p, ay, neg_by);
        let neg_uy = cneg(d, p, uy);
        let neg_dy = cneg(d, p, dy);
        let wy = cadd(d, p, cy, neg_dy);
        let claim_y = equiv(d, p, wy, neg_uy);

        and_intro(d, p, claim_x, claim_y, hwx, hwy)
    };

    // fact_z_negv : CPoint.Equiv (sub D A) (neg (sub B C))
    let fact_z_negv = {
        let neg_cx = cneg(d, p, cx);
        let vx = cadd(d, p, bx, neg_cx);
        let neg_vx = cneg(d, p, vx);
        let neg_ax = cneg(d, p, ax);
        let zx = cadd(d, p, dx, neg_ax);
        let claim_x = equiv(d, p, zx, neg_vx);

        let neg_cy = cneg(d, p, cy);
        let vy = cadd(d, p, by, neg_cy);
        let neg_vy = cneg(d, p, vy);
        let neg_ay = cneg(d, p, ay);
        let zy = cadd(d, p, dy, neg_ay);
        let claim_y = equiv(d, p, zy, neg_vy);

        and_intro(d, p, claim_x, claim_y, hzx, hzy)
    };

    // Equiv (distSq C D) (distSq A B), via dot(X,X) ~ dot(-X,-X).
    let cd_eq_ab = {
        let step1 = d.lemma(
            p.dot_congr,
            &[sub_cd, neg_u, sub_cd, neg_u, fact_w_negu, fact_w_negu],
        );
        let step2 = dot_neg_neg_proof(d, p, sub_ab);
        let dot_cdcd = dotp(d, p, sub_cd, sub_cd);
        let dot_negu_negu = dotp(d, p, neg_u, neg_u);
        let dot_abab = dotp(d, p, sub_ab, sub_ab);
        chain(d, p, dot_cdcd, &[(dot_negu_negu, step1), (dot_abab, step2)])
    };

    // Equiv (distSq D A) (distSq B C), via dot(X,X) ~ dot(-X,-X).
    let da_eq_bc = {
        let step1 = d.lemma(
            p.dot_congr,
            &[sub_da, neg_v, sub_da, neg_v, fact_z_negv, fact_z_negv],
        );
        let step2 = dot_neg_neg_proof(d, p, sub_bc);
        let dot_dada = dotp(d, p, sub_da, sub_da);
        let dot_negv_negv = dotp(d, p, neg_v, neg_v);
        let dot_bcbc = dotp(d, p, sub_bc, sub_bc);
        chain(d, p, dot_dada, &[(dot_negv_negv, step1), (dot_bcbc, step2)])
    };

    let dsq_cd = d.const_app(p.dist_sq, &[pc, pd]);
    let dsq_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dsq_da = d.const_app(p.dist_sq, &[pd, pa]);
    let dsq_bc = d.const_app(p.dist_sq, &[pb, pc]);
    let concl_cd = equiv(d, p, dsq_cd, dsq_ab);
    let concl_da = equiv(d, p, dsq_da, dsq_bc);
    let proof = and_intro(d, p, concl_cd, concl_da, cd_eq_ab, da_eq_bc);

    let ty_body = {
        let concl = d.and(concl_cd, concl_da);
        d.arrow(hyp_ty, concl)
    };
    let ty = {
        let w4 = d.pi_fv(e_fv, point, ty_body);
        let w3 = d.pi_fv(c_fv, point, w4);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h_fv, hyp_ty, proof);
        let w4 = d.lam_fv(e_fv, point, inner);
        let w3 = d.lam_fv(c_fv, point, w4);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.parallelogram_opposite_sides_eq,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the parallelogram law ---------------------------------------------------

/// Given opaque `CReal` terms `a, b, c`, proves
/// `Equiv (add (add a (add b (add b c))) (add c (add (neg b) (add (neg b) a))))
///        (add (add a a) (add c c))`,
/// i.e. `(a + 2b + c) + (c - 2b + a) ~ 2a + 2c` (`2X` written `X+X`) — pure
/// `CReal` ring algebra in three opaque terms, no reference to `dot` or
/// `CPoint`. This is the final combination step
/// [`CPointPrelude::parallelogram_law`] needs after expanding both
/// diagonals via [`CPointPrelude::dot_self_add`]/[`CPointPrelude::dot_self_sub`]:
/// `a := dot U U`, `b := dot U V`, `c := dot V V`.
fn sum_of_squares_combine_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let creal = p.creal;
    let nb = cneg(d, p, b);
    let bc = cadd(d, p, b, c);
    let b_bc = cadd(d, p, b, bc); // b + (b + c)
    let term1 = cadd(d, p, a, b_bc); // a + (b + (b + c))
    let nba = cadd(d, p, nb, a);
    let nb_nba = cadd(d, p, nb, nba); // -b + (-b + a)
    let term2 = cadd(d, p, c, nb_nba); // c + (-b + (-b + a))
    let lhs = cadd(d, p, term1, term2);

    // swap1 : lhs ~ (a + c) + (b_bc + nb_nba)
    let ac = cadd(d, p, a, c);
    let inner0 = cadd(d, p, b_bc, nb_nba);
    let swap1 = add_middle_swap_proof(d, p, a, b_bc, c, nb_nba);
    let after_swap1 = cadd(d, p, ac, inner0);

    // b_bc ~ (b+b)+c
    let bb = cadd(d, p, b, b);
    let bb_c = cadd(d, p, bb, c);
    let assoc_b = d.lemma(creal.add_assoc, &[b, b, c]); // Equiv(bb_c, b_bc)
    let s1 = symm(d, p, bb_c, b_bc, assoc_b); // Equiv(b_bc, bb_c)

    // nb_nba ~ (-b+-b)+a
    let nbnb = cadd(d, p, nb, nb);
    let nbnb_a = cadd(d, p, nbnb, a);
    let assoc_nb = d.lemma(creal.add_assoc, &[nb, nb, a]); // Equiv(nbnb_a, nb_nba)
    let s2 = symm(d, p, nbnb_a, nb_nba, assoc_nb); // Equiv(nb_nba, nbnb_a)

    let inner1 = cadd(d, p, bb_c, nbnb_a);
    let congr_inner = d.lemma(creal.add_congr, &[b_bc, bb_c, nb_nba, nbnb_a, s1, s2]); // Equiv(inner0, inner1)

    // swap2 : inner1 ~ (bb + nbnb) + (c + a)
    let bb_nbnb = cadd(d, p, bb, nbnb);
    let ca = cadd(d, p, c, a);
    let swap2 = add_middle_swap_proof(d, p, bb, c, nbnb, a); // (bb+c)+(nbnb+a) ~ (bb+nbnb)+(c+a)
    let inner2 = cadd(d, p, bb_nbnb, ca);

    // bb + nbnb ~ zero
    let zero = czero(d, p);
    let neg_bb = cneg(d, p, bb);
    let na = neg_add_proof(d, p, b, b); // Equiv(neg_bb, add nb nb) = Equiv(neg_bb, nbnb)
    let na_symm = symm(d, p, neg_bb, nbnb, na); // Equiv(nbnb, neg_bb)
    let refl_bb = refl(d, p, bb);
    let congr_bbnbnb = d.lemma(creal.add_congr, &[bb, bb, nbnb, neg_bb, refl_bb, na_symm]); // Equiv(bb_nbnb, add bb neg_bb)
    let bb_negbb = cadd(d, p, bb, neg_bb);
    let an_bb = d.lemma(creal.add_neg, &[bb]); // Equiv(bb_negbb, zero)
    let bb_nbnb_reduce = chain(d, p, bb_nbnb, &[(bb_negbb, congr_bbnbnb), (zero, an_bb)]); // Equiv(bb_nbnb, zero)

    // inner2 ~ zero + ca ~ ca ~ ac
    let refl_ca = refl(d, p, ca);
    let congr_inner2 = d.lemma(
        creal.add_congr,
        &[bb_nbnb, zero, ca, ca, bb_nbnb_reduce, refl_ca],
    ); // Equiv(inner2, add zero ca)
    let zero_ca = cadd(d, p, zero, ca);
    let za = zero_add_proof(d, p, ca); // Equiv(zero_ca, ca)
    let comm_ca = d.lemma(creal.add_comm, &[c, a]); // Equiv(ca, ac)
    let inner_reduce = chain(
        d,
        p,
        inner0,
        &[
            (inner1, congr_inner),
            (inner2, swap2),
            (zero_ca, congr_inner2),
            (ca, za),
            (ac, comm_ca),
        ],
    ); // Equiv(inner0, ac)

    // combine: lhs ~ (a+c) + inner0 ~ (a+c) + ac ~ (a+a)+(c+c)
    let refl_ac = refl(d, p, ac);
    let combined = d.lemma(
        creal.add_congr,
        &[ac, ac, inner0, ac, refl_ac, inner_reduce],
    ); // Equiv(after_swap1, add ac ac)
    let ac_ac = cadd(d, p, ac, ac);

    let final_swap = add_middle_swap_proof(d, p, a, c, a, c); // (a+c)+(a+c) ~ (a+a)+(c+c)
    let aa = cadd(d, p, a, a);
    let cc = cadd(d, p, c, c);
    let target = cadd(d, p, aa, cc);

    chain(
        d,
        p,
        lhs,
        &[
            (after_swap1, swap1),
            (ac_ac, combined),
            (target, final_swap),
        ],
    )
}

/// **The parallelogram law.** See [`CPointPrelude::parallelogram_law`].
fn declare_parallelogram_law(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    // The fourth point ("D"); named `e_fv` so the local `d` (the `IntDev`
    // builder) is never shadowed, matching the sibling declares' convention.
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

    let sub_ba = psub(d, p, pb, pa);
    let sub_cd = psub(d, p, pc, pd);
    let hyp_ty = d.const_app(p.point_equiv, &[sub_ba, sub_cd]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let ex_ty = {
        let neg_ax = cneg(d, p, ax);
        let lhs = cadd(d, p, bx, neg_ax);
        let neg_dx = cneg(d, p, dx);
        let rhs = cadd(d, p, cx, neg_dx);
        equiv(d, p, lhs, rhs)
    };
    let ey_ty = {
        let neg_ay = cneg(d, p, ay);
        let lhs = cadd(d, p, by, neg_ay);
        let neg_dy = cneg(d, p, dy);
        let rhs = cadd(d, p, cy, neg_dy);
        equiv(d, p, lhs, rhs)
    };
    let hx = d.and_left(ex_ty, ey_ty, h);
    let hy = d.and_right(ex_ty, ey_ty, h);

    // CD ~ -(AB), per coordinate (u := sub A B).
    let hwx = opposite_side_neg_scalar_proof(d, p, ax, bx, cx, dx, hx);
    let hwy = opposite_side_neg_scalar_proof(d, p, ay, by, cy, dy, hy);

    // DA ~ -(BC), per coordinate (v := sub B C), reusing the CD ~ -(AB) facts.
    let hzx = diag_side_neg_scalar_proof(d, p, ax, bx, cx, dx, hwx);
    let hzy = diag_side_neg_scalar_proof(d, p, ay, by, cy, dy, hwy);

    let sub_ab = psub(d, p, pa, pb); // u
    let sub_bc = psub(d, p, pb, pc); // v
    let sub_da = psub(d, p, pd, pa);
    let neg_u = pneg(d, p, sub_ab);
    let neg_v = pneg(d, p, sub_bc);

    // fact_w_negu : CPoint.Equiv (sub C D) (neg (sub A B)) -- identical
    // construction to `declare_parallelogram_opposite_sides_eq`'s.
    let fact_w_negu = {
        let neg_bx = cneg(d, p, bx);
        let ux = cadd(d, p, ax, neg_bx);
        let neg_ux = cneg(d, p, ux);
        let neg_dx = cneg(d, p, dx);
        let wx = cadd(d, p, cx, neg_dx);
        let claim_x = equiv(d, p, wx, neg_ux);

        let neg_by = cneg(d, p, by);
        let uy = cadd(d, p, ay, neg_by);
        let neg_uy = cneg(d, p, uy);
        let neg_dy = cneg(d, p, dy);
        let wy = cadd(d, p, cy, neg_dy);
        let claim_y = equiv(d, p, wy, neg_uy);

        and_intro(d, p, claim_x, claim_y, hwx, hwy)
    };

    // fact_z_negv : CPoint.Equiv (sub D A) (neg (sub B C)).
    let fact_z_negv = {
        let neg_cx = cneg(d, p, cx);
        let vx = cadd(d, p, bx, neg_cx);
        let neg_vx = cneg(d, p, vx);
        let neg_ax = cneg(d, p, ax);
        let zx = cadd(d, p, dx, neg_ax);
        let claim_x = equiv(d, p, zx, neg_vx);

        let neg_cy = cneg(d, p, cy);
        let vy = cadd(d, p, by, neg_cy);
        let neg_vy = cneg(d, p, vy);
        let neg_ay = cneg(d, p, ay);
        let zy = cadd(d, p, dy, neg_ay);
        let claim_y = equiv(d, p, zy, neg_vy);

        and_intro(d, p, claim_x, claim_y, hzx, hzy)
    };

    // Equiv (distSq C D) (distSq A B), via dot(X,X) ~ dot(-X,-X).
    let dot_abab = dotp(d, p, sub_ab, sub_ab);
    let dot_bcbc = dotp(d, p, sub_bc, sub_bc);
    let dot_cdcd = dotp(d, p, sub_cd, sub_cd);
    let dot_dada = dotp(d, p, sub_da, sub_da);
    let cd_eq_ab = {
        let dot_negu_negu = dotp(d, p, neg_u, neg_u);
        let step1 = d.lemma(
            p.dot_congr,
            &[sub_cd, neg_u, sub_cd, neg_u, fact_w_negu, fact_w_negu],
        );
        let step2 = dot_neg_neg_proof(d, p, sub_ab);
        chain(d, p, dot_cdcd, &[(dot_negu_negu, step1), (dot_abab, step2)])
    };

    // Equiv (distSq D A) (distSq B C), via dot(X,X) ~ dot(-X,-X).
    let da_eq_bc = {
        let dot_negv_negv = dotp(d, p, neg_v, neg_v);
        let step1 = d.lemma(
            p.dot_congr,
            &[sub_da, neg_v, sub_da, neg_v, fact_z_negv, fact_z_negv],
        );
        let step2 = dot_neg_neg_proof(d, p, sub_bc);
        chain(d, p, dot_dada, &[(dot_negv_negv, step1), (dot_bcbc, step2)])
    };

    // fact_ac : CPoint.Equiv (sub A C) (add (sub A B) (sub B C)) -- the
    // diagonal telescope, unconditional (no hypothesis needed).
    let sub_ac = psub(d, p, pa, pc);
    let padd_ab_bc = padd(d, p, sub_ab, sub_bc);
    let fact_ac = {
        let tel_x = telescope_scalar_proof(d, p, ax, bx, cx);
        let tel_y = telescope_scalar_proof(d, p, ay, by, cy);
        let neg_cx = cneg(d, p, cx);
        let acx = cadd(d, p, ax, neg_cx);
        let neg_bx = cneg(d, p, bx);
        let ux = cadd(d, p, ax, neg_bx);
        let vx = cadd(d, p, bx, neg_cx);
        let uvx = cadd(d, p, ux, vx);
        let claim_x = equiv(d, p, acx, uvx);

        let neg_cy = cneg(d, p, cy);
        let acy = cadd(d, p, ay, neg_cy);
        let neg_by = cneg(d, p, by);
        let uy = cadd(d, p, ay, neg_by);
        let vy = cadd(d, p, by, neg_cy);
        let uvy = cadd(d, p, uy, vy);
        let claim_y = equiv(d, p, acy, uvy);
        and_intro(d, p, claim_x, claim_y, tel_x, tel_y)
    };

    // fact_bd : CPoint.Equiv (sub B D) (sub (sub B C) (sub A B)) -- the other
    // diagonal telescopes to `v + (C-D)`, and `C-D ~ -(A-B)` (`hwx`/`hwy`)
    // turns that into `v - u`.
    let sub_bd = psub(d, p, pb, pd);
    let sub_bcab = psub(d, p, sub_bc, sub_ab);
    let fact_bd = {
        let tel_x = telescope_scalar_proof(d, p, bx, cx, dx); // Equiv(bdx, vx+(cx+neg dx))
        let neg_cx = cneg(d, p, cx);
        let vx = cadd(d, p, bx, neg_cx);
        let neg_dx = cneg(d, p, dx);
        let cx_ndx = cadd(d, p, cx, neg_dx);
        let neg_bx = cneg(d, p, bx);
        let ux = cadd(d, p, ax, neg_bx);
        let neg_ux = cneg(d, p, ux);
        let refl_vx = refl(d, p, vx);
        let congr_x = d.lemma(creal.add_congr, &[vx, vx, cx_ndx, neg_ux, refl_vx, hwx]);
        let bdx = cadd(d, p, bx, neg_dx);
        let vx_cxndx = cadd(d, p, vx, cx_ndx);
        let vx_negux = cadd(d, p, vx, neg_ux);
        let full_x = chain(d, p, bdx, &[(vx_cxndx, tel_x), (vx_negux, congr_x)]);

        let tel_y = telescope_scalar_proof(d, p, by, cy, dy);
        let neg_cy = cneg(d, p, cy);
        let vy = cadd(d, p, by, neg_cy);
        let neg_dy = cneg(d, p, dy);
        let cy_ndy = cadd(d, p, cy, neg_dy);
        let neg_by = cneg(d, p, by);
        let uy = cadd(d, p, ay, neg_by);
        let neg_uy = cneg(d, p, uy);
        let refl_vy = refl(d, p, vy);
        let congr_y = d.lemma(creal.add_congr, &[vy, vy, cy_ndy, neg_uy, refl_vy, hwy]);
        let bdy = cadd(d, p, by, neg_dy);
        let vy_cyndy = cadd(d, p, vy, cy_ndy);
        let vy_neguy = cadd(d, p, vy, neg_uy);
        let full_y = chain(d, p, bdy, &[(vy_cyndy, tel_y), (vy_neguy, congr_y)]);

        let claim_x = equiv(d, p, bdx, vx_negux);
        let claim_y = equiv(d, p, bdy, vy_neguy);
        and_intro(d, p, claim_x, claim_y, full_x, full_y)
    };

    // AC diagonal: dot(sub_ac,sub_ac) ~ dot_self_add(u,v).
    let dot_ab_bc = dotp(d, p, sub_ab, sub_bc); // "uv"
    let dot_ac_ac = dotp(d, p, sub_ac, sub_ac);
    let dot_padd_padd = dotp(d, p, padd_ab_bc, padd_ab_bc);
    let ac_congr = d.lemma(
        p.dot_congr,
        &[sub_ac, padd_ab_bc, sub_ac, padd_ab_bc, fact_ac, fact_ac],
    );
    let ac_expand = d.lemma(p.dot_self_add, &[sub_ab, sub_bc]);
    let ac_inner = cadd(d, p, dot_ab_bc, dot_bcbc);
    let ac_mid = cadd(d, p, dot_ab_bc, ac_inner);
    let ac_target = cadd(d, p, dot_abab, ac_mid);
    let ac_total = chain(
        d,
        p,
        dot_ac_ac,
        &[(dot_padd_padd, ac_congr), (ac_target, ac_expand)],
    );

    // BD diagonal: dot(sub_bd,sub_bd) ~ dot_self_sub(v,u), then fold `dot v u`
    // back to `dot u v`.
    let dot_bc_ab = dotp(d, p, sub_bc, sub_ab); // "vu"
    let dot_bd_bd = dotp(d, p, sub_bd, sub_bd);
    let dot_bcab_bcab = dotp(d, p, sub_bcab, sub_bcab);
    let bd_congr = d.lemma(
        p.dot_congr,
        &[sub_bd, sub_bcab, sub_bd, sub_bcab, fact_bd, fact_bd],
    );
    let bd_expand = d.lemma(p.dot_self_sub, &[sub_bc, sub_ab]);
    let neg_dot_bc_ab = cneg(d, p, dot_bc_ab);
    let bd_inner = cadd(d, p, neg_dot_bc_ab, dot_abab);
    let bd_mid = cadd(d, p, neg_dot_bc_ab, bd_inner);
    let bd_expand_target = cadd(d, p, dot_bcbc, bd_mid);

    let comm_vu = d.lemma(p.dot_comm, &[sub_bc, sub_ab]); // Equiv(dot_bc_ab, dot_ab_bc)
    let neg_congr_vu = d.lemma(creal.neg_congr, &[dot_bc_ab, dot_ab_bc, comm_vu]); // Equiv(neg_dot_bc_ab, neg_dot_ab_bc)
    let neg_dot_ab_bc = cneg(d, p, dot_ab_bc);
    let refl_dotabab = refl(d, p, dot_abab);
    let neg_bcab_abab = cadd(d, p, neg_dot_bc_ab, dot_abab);
    let neg_abbc_abab = cadd(d, p, neg_dot_ab_bc, dot_abab);
    let inner_congr = d.lemma(
        creal.add_congr,
        &[
            neg_dot_bc_ab,
            neg_dot_ab_bc,
            dot_abab,
            dot_abab,
            neg_congr_vu,
            refl_dotabab,
        ],
    ); // Equiv(neg_bcab_abab, neg_abbc_abab)
    let neg_bcab_full = cadd(d, p, neg_dot_bc_ab, neg_bcab_abab);
    let neg_abbc_full = cadd(d, p, neg_dot_ab_bc, neg_abbc_abab);
    let outer_congr = d.lemma(
        creal.add_congr,
        &[
            neg_dot_bc_ab,
            neg_dot_ab_bc,
            neg_bcab_abab,
            neg_abbc_abab,
            neg_congr_vu,
            inner_congr,
        ],
    ); // Equiv(neg_bcab_full, neg_abbc_full)
    let refl_bcbc = refl(d, p, dot_bcbc);
    let bd_final_target = cadd(d, p, dot_bcbc, neg_abbc_full);
    let top_congr = d.lemma(
        creal.add_congr,
        &[
            dot_bcbc,
            dot_bcbc,
            neg_bcab_full,
            neg_abbc_full,
            refl_bcbc,
            outer_congr,
        ],
    ); // Equiv(bd_expand_target, bd_final_target)

    let bd_total = chain(
        d,
        p,
        dot_bd_bd,
        &[
            (dot_bcab_bcab, bd_congr),
            (bd_expand_target, bd_expand),
            (bd_final_target, top_congr),
        ],
    );

    // T := distSq A C + distSq B D ~ (dot_abab+dot_abab)+(dot_bcbc+dot_bcbc).
    let t_raw = cadd(d, p, dot_ac_ac, dot_bd_bd);
    let t_congr = d.lemma(
        creal.add_congr,
        &[
            dot_ac_ac,
            ac_target,
            dot_bd_bd,
            bd_final_target,
            ac_total,
            bd_total,
        ],
    );
    let combine_lhs = cadd(d, p, ac_target, bd_final_target);
    let combine_result = sum_of_squares_combine_proof(d, p, dot_abab, dot_ab_bc, dot_bcbc);
    let abab_abab = cadd(d, p, dot_abab, dot_abab);
    let bcbc_bcbc = cadd(d, p, dot_bcbc, dot_bcbc);
    let target_mid = cadd(d, p, abab_abab, bcbc_bcbc);
    let t_total = chain(
        d,
        p,
        t_raw,
        &[(combine_lhs, t_congr), (target_mid, combine_result)],
    );

    // S := distSq A B + distSq B C + distSq C D + distSq D A
    //   ~ ((dot_abab+dot_bcbc)+dot_abab)+dot_bcbc ~ (dot_abab+dot_bcbc)+(dot_abab+dot_bcbc)
    //   ~ (dot_abab+dot_abab)+(dot_bcbc+dot_bcbc) = target_mid.
    let ab_bc = cadd(d, p, dot_abab, dot_bcbc);
    let ab_bc_cdcd = cadd(d, p, ab_bc, dot_cdcd);
    let s_raw = cadd(d, p, ab_bc_cdcd, dot_dada);
    let refl_abbc = refl(d, p, ab_bc);
    let ab_bc_abab = cadd(d, p, ab_bc, dot_abab);
    let combine_c = d.lemma(
        creal.add_congr,
        &[ab_bc, ab_bc, dot_cdcd, dot_abab, refl_abbc, cd_eq_ab],
    ); // Equiv(ab_bc_cdcd, ab_bc_abab)
    let refl_dada = refl(d, p, dot_dada);
    let mid1 = cadd(d, p, ab_bc_abab, dot_dada);
    let lift_c = d.lemma(
        creal.add_congr,
        &[
            ab_bc_cdcd, ab_bc_abab, dot_dada, dot_dada, combine_c, refl_dada,
        ],
    ); // Equiv(s_raw, mid1)

    let refl_ababc = refl(d, p, ab_bc_abab);
    let s1 = cadd(d, p, ab_bc_abab, dot_bcbc); // ((uu+vv)+uu)+vv
    let combine_d = d.lemma(
        creal.add_congr,
        &[
            ab_bc_abab, ab_bc_abab, dot_dada, dot_bcbc, refl_ababc, da_eq_bc,
        ],
    ); // Equiv(mid1, s1)

    let assoc_s = d.lemma(creal.add_assoc, &[ab_bc, dot_abab, dot_bcbc]); // Equiv(s1, ab_bc+(dot_abab+dot_bcbc))
    let abab_bcbc = cadd(d, p, dot_abab, dot_bcbc);
    let s2 = cadd(d, p, ab_bc, abab_bcbc);
    let swap_s = add_middle_swap_proof(d, p, dot_abab, dot_bcbc, dot_abab, dot_bcbc); // (uu+vv)+(uu+vv) ~ (uu+uu)+(vv+vv)

    // s_total : Equiv(s_raw, target_mid).
    let s_total = chain(
        d,
        p,
        s_raw,
        &[
            (mid1, lift_c),
            (s1, combine_d),
            (s2, assoc_s),
            (target_mid, swap_s),
        ],
    );

    // t_total : Equiv(t_raw, target_mid) (established above); flip it and
    // chain onto s_total to get Equiv(s_raw, t_raw) = Equiv(S, T).
    let t_total_symm = symm(d, p, t_raw, target_mid, t_total); // Equiv(target_mid, t_raw)
    let final_proof = chain(d, p, s_raw, &[(target_mid, s_total), (t_raw, t_total_symm)]);

    let dsq_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dsq_bc = d.const_app(p.dist_sq, &[pb, pc]);
    let dsq_cd = d.const_app(p.dist_sq, &[pc, pd]);
    let dsq_da = d.const_app(p.dist_sq, &[pd, pa]);
    let dsq_ac = d.const_app(p.dist_sq, &[pa, pc]);
    let dsq_bd = d.const_app(p.dist_sq, &[pb, pd]);
    let dsq_ab_bc = cadd(d, p, dsq_ab, dsq_bc);
    let dsq_ab_bc_cd = cadd(d, p, dsq_ab_bc, dsq_cd);
    let s_named = cadd(d, p, dsq_ab_bc_cd, dsq_da);
    let t_named = cadd(d, p, dsq_ac, dsq_bd);

    let ty_body = {
        let concl = equiv(d, p, s_named, t_named);
        d.arrow(hyp_ty, concl)
    };
    let ty = {
        let w4 = d.pi_fv(e_fv, point, ty_body);
        let w3 = d.pi_fv(c_fv, point, w4);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h_fv, hyp_ty, final_proof);
        let w4 = d.lam_fv(e_fv, point, inner);
        let w3 = d.lam_fv(c_fv, point, w4);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.parallelogram_law,
        uparams: vec![],
        ty,
        value,
    })
}

// --- generic right-chain flatten/reorder machinery --------------------------
//
// Euler's quadrilateral theorem's combination step needs to show that two
// differently-associated, differently-ordered sums of the same twelve
// `CReal` terms (with repeats: six atoms, each appearing twice) are `Equiv`.
// This file's existing combine proofs (`sum_of_squares_combine_proof`,
// `apollonius_combine_proof`) hand-derive exactly this kind of
// `add_assoc`/`add_comm` bookkeeping for three and six terms respectively;
// at twelve terms doing it by hand is mechanical enough, and error-prone
// enough, to be worth writing once generically instead. No cancellation is
// needed anywhere below — this is pure commutative-monoid rearrangement.

/// A binary tree of `CReal.add` applications with `CReal`-valued leaves,
/// mirroring the shape of an already-built nested sum so a flattening proof
/// can be derived by walking the same structure.
#[derive(Clone)]
enum SumTree {
    Leaf(ExprId),
    Add(Box<SumTree>, Box<SumTree>),
}

fn sadd(l: SumTree, r: SumTree) -> SumTree {
    SumTree::Add(Box::new(l), Box::new(r))
}

/// The actual (arbitrarily-nested) `CReal` term this tree denotes.
fn sum_tree_build(d: &mut IntDev<'_>, p: CPointPrelude, t: &SumTree) -> ExprId {
    match t {
        SumTree::Leaf(x) => *x,
        SumTree::Add(l, r) => {
            let lx = sum_tree_build(d, p, l);
            let rx = sum_tree_build(d, p, r);
            cadd(d, p, lx, rx)
        }
    }
}

/// The leaves, left to right.
fn sum_tree_leaves(t: &SumTree, out: &mut Vec<ExprId>) {
    match t {
        SumTree::Leaf(x) => out.push(*x),
        SumTree::Add(l, r) => {
            sum_tree_leaves(l, out);
            sum_tree_leaves(r, out);
        }
    }
}

/// Build the fully right-associated chain `x0+(x1+(...+xn))` of a nonempty
/// leaf list.
fn build_right_chain(d: &mut IntDev<'_>, p: CPointPrelude, xs: &[ExprId]) -> ExprId {
    match xs {
        [] => unreachable!("build_right_chain: empty leaf list"),
        [x] => *x,
        [x, rest @ ..] => {
            let tail = build_right_chain(d, p, rest);
            cadd(d, p, *x, tail)
        }
    }
}

/// Given the leaves `xs` of a right-associated chain `l_chain =
/// build_right_chain(xs)` and an already right-associated chain `r_chain`,
/// proves `Equiv (add l_chain r_chain) result`, where `result` is the single
/// right-associated chain of `xs` followed by `r_chain`'s own leaves.
fn concat_right_chains(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    xs: &[ExprId],
    r_chain: ExprId,
) -> (ExprId, ExprId) {
    let creal = p.creal;
    match xs {
        [] => unreachable!("concat_right_chains: empty leaf list"),
        [x] => {
            let result = cadd(d, p, *x, r_chain);
            (result, refl(d, p, result))
        }
        [x, rest @ ..] => {
            let tail = build_right_chain(d, p, rest);
            let l_chain = cadd(d, p, *x, tail);
            let start = cadd(d, p, l_chain, r_chain); // (x+tail)+r_chain
            let assoc = d.lemma(creal.add_assoc, &[*x, tail, r_chain]); // Equiv(start, x+(tail+r_chain))
            let tail_r = cadd(d, p, tail, r_chain);
            let (tail_result, tail_proof) = concat_right_chains(d, p, rest, r_chain); // Equiv(tail_r, tail_result)
            let refl_x = refl(d, p, *x);
            let congr = d.lemma(
                creal.add_congr,
                &[*x, *x, tail_r, tail_result, refl_x, tail_proof],
            );
            let mid = cadd(d, p, *x, tail_r);
            let result = cadd(d, p, *x, tail_result);
            let proof = chain(d, p, start, &[(mid, assoc), (result, congr)]);
            (result, proof)
        }
    }
}

/// Flatten an arbitrarily-nested sum tree into the right-associated chain of
/// its leaves (left to right), returning that chain and a proof the original
/// nested term equals it.
fn flatten_sum_tree(d: &mut IntDev<'_>, p: CPointPrelude, t: &SumTree) -> (ExprId, ExprId) {
    match t {
        SumTree::Leaf(x) => (*x, refl(d, p, *x)),
        SumTree::Add(l, r) => {
            let creal = p.creal;
            let l_expr = sum_tree_build(d, p, l);
            let r_expr = sum_tree_build(d, p, r);
            let original = cadd(d, p, l_expr, r_expr);
            let (l_chain, l_proof) = flatten_sum_tree(d, p, l);
            let (r_chain, r_proof) = flatten_sum_tree(d, p, r);
            let step1 = d.lemma(
                creal.add_congr,
                &[l_expr, l_chain, r_expr, r_chain, l_proof, r_proof],
            ); // Equiv(original, l_chain + r_chain)
            let mid = cadd(d, p, l_chain, r_chain);
            let mut l_leaves = Vec::new();
            sum_tree_leaves(l, &mut l_leaves);
            let (result, concat_proof) = concat_right_chains(d, p, &l_leaves, r_chain);
            let proof = chain(d, p, original, &[(mid, step1), (result, concat_proof)]);
            (result, proof)
        }
    }
}

/// `Equiv (build_right_chain w) (build_right_chain w')`, `w'` being `w` with
/// positions `0` and `1` swapped (`w.len() >= 2`).
fn swap_head01(d: &mut IntDev<'_>, p: CPointPrelude, w: &[ExprId]) -> ExprId {
    let creal = p.creal;
    match w {
        [a, b] => d.lemma(creal.add_comm, &[*a, *b]), // Equiv(a+b, b+a)
        [a, b, rest @ ..] => {
            // a+(b+r) ~ (a+b)+r ~ (b+a)+r ~ b+(a+r)
            let r = build_right_chain(d, p, rest);
            let br = cadd(d, p, *b, r);
            let start = cadd(d, p, *a, br); // a+(b+r)
            let ab = cadd(d, p, *a, *b);
            let assoc1 = d.lemma(creal.add_assoc, &[*a, *b, r]); // Equiv(ab+r, a+(b+r))
            let ab_r = cadd(d, p, ab, r);
            let assoc1_symm = symm(d, p, ab_r, start, assoc1); // Equiv(start, ab_r)
            let ba = cadd(d, p, *b, *a);
            let comm = d.lemma(creal.add_comm, &[*a, *b]); // Equiv(ab, ba)
            let refl_r = refl(d, p, r);
            let congr = d.lemma(creal.add_congr, &[ab, ba, r, r, comm, refl_r]); // Equiv(ab_r, ba+r)
            let ba_r = cadd(d, p, ba, r);
            let assoc2 = d.lemma(creal.add_assoc, &[*b, *a, r]); // Equiv(ba_r, b+(a+r))
            let ar = cadd(d, p, *a, r);
            let target = cadd(d, p, *b, ar);
            chain(
                d,
                p,
                start,
                &[(ab_r, assoc1_symm), (ba_r, congr), (target, assoc2)],
            )
        }
        _ => unreachable!("swap_head01: needs at least 2 elements"),
    }
}

/// `Equiv (build_right_chain w) (build_right_chain w')`, `w'` being `w` with
/// positions `i` and `i+1` swapped.
fn adjacent_swap_at(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    w: &[ExprId],
    i: usize,
) -> (Vec<ExprId>, ExprId) {
    let creal = p.creal;
    if i == 0 {
        let proof = swap_head01(d, p, w);
        let mut w2 = w.to_vec();
        w2.swap(0, 1);
        (w2, proof)
    } else {
        let w0 = w[0];
        let rest = &w[1..];
        let rest_chain = build_right_chain(d, p, rest);
        let (rest2, rest_proof) = adjacent_swap_at(d, p, rest, i - 1); // Equiv(rest_chain, rest_chain2)
        let rest_chain2 = build_right_chain(d, p, &rest2);
        let refl_w0 = refl(d, p, w0);
        let congr = d.lemma(
            creal.add_congr,
            &[w0, w0, rest_chain, rest_chain2, refl_w0, rest_proof],
        );
        let mut w2 = w.to_vec();
        w2.swap(i, i + 1);
        (w2, congr)
    }
}

/// `Equiv (build_right_chain from) (build_right_chain to)`, given `to` is a
/// permutation of `from` (an internal-consistency `expect`, not a user-facing
/// contract, catches it otherwise). Selection-sort via adjacent
/// transpositions: for each target position, bubble the matching leaf up
/// from wherever it currently sits.
fn reorder_right_chain(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    from: &[ExprId],
    to: &[ExprId],
) -> ExprId {
    assert_eq!(from.len(), to.len(), "reorder_right_chain: length mismatch");
    let mut w = from.to_vec();
    let start = build_right_chain(d, p, &w);
    let mut proof = refl(d, p, start);
    let mut current = start;
    for (i, target) in to.iter().enumerate() {
        // `w[0..i]` already matches `to[0..i]`; find `target` in the
        // remaining suffix and bubble it down to position `i` via adjacent
        // swaps, never touching the already-placed prefix (every swap index
        // below stays `>= i`).
        let j = (i..w.len())
            .find(|&k| w[k] == *target)
            .expect("reorder_right_chain: `to` is not a permutation of `from`");
        let mut k = j;
        while k > i {
            let (w2, step_proof) = adjacent_swap_at(d, p, &w, k - 1);
            let next = build_right_chain(d, p, &w2);
            proof = d.lemma(
                p.creal.equiv_trans,
                &[start, current, next, proof, step_proof],
            );
            current = next;
            w = w2;
            k -= 1;
        }
    }
    proof
}

/// **Euler's quadrilateral theorem, unconditional.** See
/// [`CPointPrelude::euler_quadrilateral`].
fn declare_euler_quadrilateral(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    // The fourth point ("D"); named `e_fv` so the local `d` (the `IntDev`
    // builder) is never shadowed, matching this file's convention.
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

    // -- x-coordinate telescoping: AC ~ u+v, BD ~ v+w, DA ~ -((u+v)+w) -------
    let neg_bx = cneg(d, p, bx);
    let ux = cadd(d, p, ax, neg_bx); // A-B, x
    let neg_cx = cneg(d, p, cx);
    let vx = cadd(d, p, bx, neg_cx); // B-C, x
    let neg_dx = cneg(d, p, dx);
    let wx = cadd(d, p, cx, neg_dx); // C-D, x

    let ax_cx = cadd(d, p, ax, neg_cx); // A-C, x
    let ux_vx = cadd(d, p, ux, vx);
    let fact_ac_x = telescope_scalar_proof(d, p, ax, bx, cx); // Equiv(ax_cx, ux_vx)

    let bx_dx = cadd(d, p, bx, neg_dx); // B-D, x
    let vx_wx = cadd(d, p, vx, wx);
    let fact_bd_x = telescope_scalar_proof(d, p, bx, cx, dx); // Equiv(bx_dx, vx_wx)

    let ax_dx = cadd(d, p, ax, neg_dx); // A-D, x
    let ax_cx_wx = cadd(d, p, ax_cx, wx);
    let tel_ad_x = telescope_scalar_proof(d, p, ax, cx, dx); // Equiv(ax_dx, ax_cx_wx)
    let refl_wx = refl(d, p, wx);
    let congr_ad_x = d.lemma(creal.add_congr, &[ax_cx, ux_vx, wx, wx, fact_ac_x, refl_wx]); // Equiv(ax_cx_wx, ux_vx_wx)
    let ux_vx_wx = cadd(d, p, ux_vx, wx); // (u+v+w)_x
    let ad_to_uvw_x = chain(d, p, ax_dx, &[(ax_cx_wx, tel_ad_x), (ux_vx_wx, congr_ad_x)]); // Equiv(ax_dx, ux_vx_wx)

    let neg_ax = cneg(d, p, ax);
    let dx_ax = cadd(d, p, dx, neg_ax); // D-A, x
    let negsubcomm_x = neg_sub_comm_scalar_proof(d, p, ax, dx); // Equiv(neg(ax_dx), dx_ax)
    let neg_ax_dx = cneg(d, p, ax_dx);
    let negsubcomm_x_symm = symm(d, p, neg_ax_dx, dx_ax, negsubcomm_x); // Equiv(dx_ax, neg_ax_dx)
    let neg_congr_ad_x = d.lemma(creal.neg_congr, &[ax_dx, ux_vx_wx, ad_to_uvw_x]); // Equiv(neg_ax_dx, neg(ux_vx_wx))
    let neg_uvw_x = cneg(d, p, ux_vx_wx);
    let fact_da_x = chain(
        d,
        p,
        dx_ax,
        &[(neg_ax_dx, negsubcomm_x_symm), (neg_uvw_x, neg_congr_ad_x)],
    ); // Equiv(dx_ax, neg_uvw_x)

    // -- y-coordinate: mirror of the above --------------------------------
    let neg_by = cneg(d, p, by);
    let uy = cadd(d, p, ay, neg_by);
    let neg_cy = cneg(d, p, cy);
    let vy = cadd(d, p, by, neg_cy);
    let neg_dy = cneg(d, p, dy);
    let wy = cadd(d, p, cy, neg_dy);

    let ay_cy = cadd(d, p, ay, neg_cy);
    let uy_vy = cadd(d, p, uy, vy);
    let fact_ac_y = telescope_scalar_proof(d, p, ay, by, cy);

    let by_dy = cadd(d, p, by, neg_dy);
    let vy_wy = cadd(d, p, vy, wy);
    let fact_bd_y = telescope_scalar_proof(d, p, by, cy, dy);

    let ay_dy = cadd(d, p, ay, neg_dy);
    let ay_cy_wy = cadd(d, p, ay_cy, wy);
    let tel_ad_y = telescope_scalar_proof(d, p, ay, cy, dy);
    let refl_wy = refl(d, p, wy);
    let congr_ad_y = d.lemma(creal.add_congr, &[ay_cy, uy_vy, wy, wy, fact_ac_y, refl_wy]);
    let uy_vy_wy = cadd(d, p, uy_vy, wy);
    let ad_to_uvw_y = chain(d, p, ay_dy, &[(ay_cy_wy, tel_ad_y), (uy_vy_wy, congr_ad_y)]);

    let neg_ay = cneg(d, p, ay);
    let dy_ay = cadd(d, p, dy, neg_ay);
    let negsubcomm_y = neg_sub_comm_scalar_proof(d, p, ay, dy);
    let neg_ay_dy = cneg(d, p, ay_dy);
    let negsubcomm_y_symm = symm(d, p, neg_ay_dy, dy_ay, negsubcomm_y);
    let neg_congr_ad_y = d.lemma(creal.neg_congr, &[ay_dy, uy_vy_wy, ad_to_uvw_y]);
    let neg_uvw_y = cneg(d, p, uy_vy_wy);
    let fact_da_y = chain(
        d,
        p,
        dy_ay,
        &[(neg_ay_dy, negsubcomm_y_symm), (neg_uvw_y, neg_congr_ad_y)],
    );

    // -- package into CPoint.Equiv facts, unconditionally --------------------
    let u = psub(d, p, pa, pb);
    let v = psub(d, p, pb, pc);
    let w_vec = psub(d, p, pc, pd);
    let uv_pt = padd(d, p, u, v); // = AC
    let vw_pt = padd(d, p, v, w_vec); // = BD
    let uvw_pt = padd(d, p, uv_pt, w_vec); // (u+v)+w
    let neg_uvw_pt = pneg(d, p, uvw_pt);
    let big_w = padd(d, p, u, w_vec); // W := (A-B)+(C-D)

    let claim_ac_x = equiv(d, p, ax_cx, ux_vx);
    let claim_ac_y = equiv(d, p, ay_cy, uy_vy);
    let fact_ac_point = and_intro(d, p, claim_ac_x, claim_ac_y, fact_ac_x, fact_ac_y);

    let claim_bd_x = equiv(d, p, bx_dx, vx_wx);
    let claim_bd_y = equiv(d, p, by_dy, vy_wy);
    let fact_bd_point = and_intro(d, p, claim_bd_x, claim_bd_y, fact_bd_x, fact_bd_y);

    let claim_da_x = equiv(d, p, dx_ax, neg_uvw_x);
    let claim_da_y = equiv(d, p, dy_ay, neg_uvw_y);
    let fact_da_point = and_intro(d, p, claim_da_x, claim_da_y, fact_da_x, fact_da_y);

    // -- dot-level: transport the diagonal/DA facts through `dot`, then -----
    // -- expand every squared length via dot_self_add/dot_self_add3 ---------
    let sub_ac = psub(d, p, pa, pc);
    let sub_bd = psub(d, p, pb, pd);
    let sub_da = psub(d, p, pd, pa); // = z

    let dot_ac_ac = dotp(d, p, sub_ac, sub_ac);
    let dot_uvuv = dotp(d, p, uv_pt, uv_pt);
    let ac_congr = d.lemma(
        p.dot_congr,
        &[sub_ac, uv_pt, sub_ac, uv_pt, fact_ac_point, fact_ac_point],
    ); // Equiv(dot_ac_ac, dot_uvuv)

    let dot_bd_bd = dotp(d, p, sub_bd, sub_bd);
    let dot_vwvw = dotp(d, p, vw_pt, vw_pt);
    let bd_congr = d.lemma(
        p.dot_congr,
        &[sub_bd, vw_pt, sub_bd, vw_pt, fact_bd_point, fact_bd_point],
    ); // Equiv(dot_bd_bd, dot_vwvw)

    let dot_da_da = dotp(d, p, sub_da, sub_da);
    let dot_neguvw_neguvw = dotp(d, p, neg_uvw_pt, neg_uvw_pt);
    let da_congr = d.lemma(
        p.dot_congr,
        &[
            sub_da,
            neg_uvw_pt,
            sub_da,
            neg_uvw_pt,
            fact_da_point,
            fact_da_point,
        ],
    ); // Equiv(dot_da_da, dot_neguvw_neguvw)
    let dot_uvwuvw = dotp(d, p, uvw_pt, uvw_pt);
    let negneg_uvw = dot_neg_neg_proof(d, p, uvw_pt); // Equiv(dot_neguvw_neguvw, dot_uvwuvw)

    let dot_ww = dotp(d, p, big_w, big_w);

    let ac_expand = d.lemma(p.dot_self_add, &[u, v]); // Equiv(dot_uvuv, M)
    let bd_expand = d.lemma(p.dot_self_add, &[v, w_vec]); // Equiv(dot_vwvw, P)
    let w_expand = d.lemma(p.dot_self_add, &[u, w_vec]); // Equiv(dot_ww, Q)
    let da_expand = d.lemma(p.dot_self_add3, &[u, v, w_vec]); // Equiv(dot_uvwuvw, E)

    // -- the atomic scalar leaves, and the trees mirroring exactly what -----
    // -- dot_self_add/dot_self_add3 produce as their conclusions ------------
    let a1 = dotp(d, p, u, u);
    let b1 = dotp(d, p, v, v);
    let c1 = dotp(d, p, w_vec, w_vec);
    let d1 = dotp(d, p, u, v);
    let d2 = dotp(d, p, u, w_vec);
    let d3 = dotp(d, p, v, w_vec);

    let m_tree = sadd(
        SumTree::Leaf(a1),
        sadd(
            SumTree::Leaf(d1),
            sadd(SumTree::Leaf(d1), SumTree::Leaf(b1)),
        ),
    );
    let p_tree = sadd(
        SumTree::Leaf(b1),
        sadd(
            SumTree::Leaf(d3),
            sadd(SumTree::Leaf(d3), SumTree::Leaf(c1)),
        ),
    );
    let q_tree = sadd(
        SumTree::Leaf(a1),
        sadd(
            SumTree::Leaf(d2),
            sadd(SumTree::Leaf(d2), SumTree::Leaf(c1)),
        ),
    );
    let n_tree = sadd(SumTree::Leaf(d2), SumTree::Leaf(d3));
    let e_tree = sadd(
        m_tree.clone(),
        sadd(n_tree.clone(), sadd(n_tree.clone(), SumTree::Leaf(c1))),
    );

    let m_expr = sum_tree_build(d, p, &m_tree);
    let p_expr = sum_tree_build(d, p, &p_tree);
    let q_expr = sum_tree_build(d, p, &q_tree);
    let e_expr = sum_tree_build(d, p, &e_tree);

    let ac_total = chain(
        d,
        p,
        dot_ac_ac,
        &[(dot_uvuv, ac_congr), (m_expr, ac_expand)],
    );
    let bd_total = chain(
        d,
        p,
        dot_bd_bd,
        &[(dot_vwvw, bd_congr), (p_expr, bd_expand)],
    );
    let w_total = w_expand; // Equiv(dot_ww, q_expr) directly (big_w IS u+w_vec)
    let da_total = chain(
        d,
        p,
        dot_da_da,
        &[
            (dot_neguvw_neguvw, da_congr),
            (dot_uvwuvw, negneg_uvw),
            (e_expr, da_expand),
        ],
    );

    // -- S := distSq A B + (distSq B C + (distSq C D + distSq D A)) ---------
    let refl_c1 = refl(d, p, c1);
    let c1_dotdada = cadd(d, p, c1, dot_da_da);
    let c1_eexpr = cadd(d, p, c1, e_expr);
    let congr1 = d.lemma(
        creal.add_congr,
        &[c1, c1, dot_da_da, e_expr, refl_c1, da_total],
    ); // Equiv(c1_dotdada, c1_eexpr)
    let refl_b1 = refl(d, p, b1);
    let b1_c1dotdada = cadd(d, p, b1, c1_dotdada);
    let b1_c1eexpr = cadd(d, p, b1, c1_eexpr);
    let congr2 = d.lemma(
        creal.add_congr,
        &[b1, b1, c1_dotdada, c1_eexpr, refl_b1, congr1],
    ); // Equiv(b1_c1dotdada, b1_c1eexpr)
    let refl_a1 = refl(d, p, a1);
    let s_raw = cadd(d, p, a1, b1_c1dotdada);
    let s_expanded = cadd(d, p, a1, b1_c1eexpr);
    let congr3 = d.lemma(
        creal.add_congr,
        &[a1, a1, b1_c1dotdada, b1_c1eexpr, refl_a1, congr2],
    ); // Equiv(s_raw, s_expanded)

    let s_tree = sadd(
        SumTree::Leaf(a1),
        sadd(SumTree::Leaf(b1), sadd(SumTree::Leaf(c1), e_tree)),
    );

    // -- T := (distSq A C + distSq B D) + dot W W ----------------------------
    let t3_raw_inner = cadd(d, p, dot_ac_ac, dot_bd_bd);
    let t3_raw = cadd(d, p, t3_raw_inner, dot_ww);
    let congr_inner = d.lemma(
        creal.add_congr,
        &[dot_ac_ac, m_expr, dot_bd_bd, p_expr, ac_total, bd_total],
    ); // Equiv(t3_raw_inner, m_expr+p_expr)
    let mp_expr = cadd(d, p, m_expr, p_expr);
    let t3_expanded = cadd(d, p, mp_expr, q_expr);
    let congr_outer = d.lemma(
        creal.add_congr,
        &[t3_raw_inner, mp_expr, dot_ww, q_expr, congr_inner, w_total],
    ); // Equiv(t3_raw, t3_expanded)

    let t3_tree = sadd(sadd(m_tree, p_tree), q_tree);

    // -- flatten both expanded sides into right-chains of the same twelve ---
    // -- leaves (a1,a1,b1,b1,c1,c1,d1,d1,d2,d2,d3,d3 in some order), and -----
    // -- reorder one into the other -----------------------------------------
    let (s_chain, s_flatten) = flatten_sum_tree(d, p, &s_tree); // Equiv(s_expanded, s_chain)
    let (t3_chain, t3_flatten) = flatten_sum_tree(d, p, &t3_tree); // Equiv(t3_expanded, t3_chain)

    let mut s_leaves = Vec::new();
    sum_tree_leaves(&s_tree, &mut s_leaves);
    let mut t3_leaves = Vec::new();
    sum_tree_leaves(&t3_tree, &mut t3_leaves);
    let reorder = reorder_right_chain(d, p, &s_leaves, &t3_leaves); // Equiv(s_chain, t3_chain)

    let t3_flatten_symm = symm(d, p, t3_expanded, t3_chain, t3_flatten); // Equiv(t3_chain, t3_expanded)
    let congr_outer_symm = symm(d, p, t3_raw, t3_expanded, congr_outer); // Equiv(t3_expanded, t3_raw)

    let final_proof = chain(
        d,
        p,
        s_raw,
        &[
            (s_expanded, congr3),
            (s_chain, s_flatten),
            (t3_chain, reorder),
            (t3_expanded, t3_flatten_symm),
        ],
    );
    let final_proof = d.lemma(
        creal.equiv_trans,
        &[s_raw, t3_expanded, t3_raw, final_proof, congr_outer_symm],
    );

    // -- state the theorem over `distSq`/`dot`, defeq to the raw form above --
    let dsq_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dsq_bc = d.const_app(p.dist_sq, &[pb, pc]);
    let dsq_cd = d.const_app(p.dist_sq, &[pc, pd]);
    let dsq_da = d.const_app(p.dist_sq, &[pd, pa]);
    let dsq_ac = d.const_app(p.dist_sq, &[pa, pc]);
    let dsq_bd = d.const_app(p.dist_sq, &[pb, pd]);
    let dot_bigw_bigw = dotp(d, p, big_w, big_w);

    let dsq_cd_da = cadd(d, p, dsq_cd, dsq_da);
    let dsq_bc_cd_da = cadd(d, p, dsq_bc, dsq_cd_da);
    let s_named = cadd(d, p, dsq_ab, dsq_bc_cd_da);
    let dsq_ac_bd = cadd(d, p, dsq_ac, dsq_bd);
    let t_named = cadd(d, p, dsq_ac_bd, dot_bigw_bigw);

    let ty_body = equiv(d, p, s_named, t_named);
    let ty = {
        let w4 = d.pi_fv(e_fv, point, ty_body);
        let w3 = d.pi_fv(c_fv, point, w4);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let w4 = d.lam_fv(e_fv, point, final_proof);
        let w3 = d.lam_fv(c_fv, point, w4);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.euler_quadrilateral,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Apollonius' median theorem.** See [`CPointPrelude::apollonius_median`].
fn declare_apollonius_median(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
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

    let pm = d.const_app(p.point_midpoint, &[pb, pc]); // M := midpoint B C
    let mx = midpoint(d, p, bx, cx);
    let my = midpoint(d, p, by, cy);

    let p_am = psub(d, p, pa, pm); // A - M
    let p_bm = psub(d, p, pb, pm); // B - M

    let neg_mx = cneg(d, p, mx);
    let amx = cadd(d, p, ax, neg_mx);
    let bmx = cadd(d, p, bx, neg_mx);
    let neg_my = cneg(d, p, my);
    let amy = cadd(d, p, ay, neg_my);
    let bmy = cadd(d, p, by, neg_my);

    // AB ~ P - D, per coordinate (P := A-M, D := B-M).
    let dd_ab_x = diff_diff_scalar_proof(d, p, ax, bx, mx); // Equiv(ax-bx, amx-bmx)
    let dd_ab_y = diff_diff_scalar_proof(d, p, ay, by, my);

    // AC ~ P + D, per coordinate: AC ~ P - (C-M), and C-M ~ -(B-M) = -D.
    let fact_ac_x = {
        let dd_ac_x = diff_diff_scalar_proof(d, p, ax, cx, mx); // Equiv(ax-cx, amx-cmx)
        let neg_mx2 = cneg(d, p, mx);
        let cmx = cadd(d, p, cx, neg_mx2);
        let negswap_x = apollonius_neg_swap_scalar_proof(d, p, bx, cx, mx); // Equiv(cmx, neg(bmx))
        let neg_cmx = cneg(d, p, cmx);
        let neg_bmx = cneg(d, p, bmx);
        let neg_neg_bmx = cneg(d, p, neg_bmx);
        let neg_congr = d.lemma(creal.neg_congr, &[cmx, neg_bmx, negswap_x]); // Equiv(neg cmx, neg(neg bmx))
        let refl_amx = refl(d, p, amx);
        let amx_cmx = cadd(d, p, amx, neg_cmx);
        let amx_negnegbmx = cadd(d, p, amx, neg_neg_bmx);
        let step1 = d.lemma(
            creal.add_congr,
            &[amx, amx, neg_cmx, neg_neg_bmx, refl_amx, neg_congr],
        );
        let nn = neg_neg_proof(d, p, bmx); // Equiv(neg(neg bmx), bmx)
        let step2 = d.lemma(creal.add_congr, &[amx, amx, neg_neg_bmx, bmx, refl_amx, nn]);
        let amx_bmx = cadd(d, p, amx, bmx);
        let neg_cx0 = cneg(d, p, cx);
        let ax_cx = cadd(d, p, ax, neg_cx0);
        chain(
            d,
            p,
            ax_cx,
            &[(amx_cmx, dd_ac_x), (amx_negnegbmx, step1), (amx_bmx, step2)],
        )
    };
    let fact_ac_y = {
        let dd_ac_y = diff_diff_scalar_proof(d, p, ay, cy, my);
        let neg_my2 = cneg(d, p, my);
        let cmy = cadd(d, p, cy, neg_my2);
        let negswap_y = apollonius_neg_swap_scalar_proof(d, p, by, cy, my);
        let neg_cmy = cneg(d, p, cmy);
        let neg_bmy = cneg(d, p, bmy);
        let neg_neg_bmy = cneg(d, p, neg_bmy);
        let neg_congr = d.lemma(creal.neg_congr, &[cmy, neg_bmy, negswap_y]);
        let refl_amy = refl(d, p, amy);
        let amy_cmy = cadd(d, p, amy, neg_cmy);
        let amy_negnegbmy = cadd(d, p, amy, neg_neg_bmy);
        let step1 = d.lemma(
            creal.add_congr,
            &[amy, amy, neg_cmy, neg_neg_bmy, refl_amy, neg_congr],
        );
        let nn = neg_neg_proof(d, p, bmy);
        let step2 = d.lemma(creal.add_congr, &[amy, amy, neg_neg_bmy, bmy, refl_amy, nn]);
        let amy_bmy = cadd(d, p, amy, bmy);
        let neg_cy0 = cneg(d, p, cy);
        let ay_cy = cadd(d, p, ay, neg_cy0);
        chain(
            d,
            p,
            ay_cy,
            &[(amy_cmy, dd_ac_y), (amy_negnegbmy, step1), (amy_bmy, step2)],
        )
    };

    // Package into CPoint.Equiv facts.
    let sub_ab = psub(d, p, pa, pb);
    let sub_ac = psub(d, p, pa, pc);
    let psub_ambm = psub(d, p, p_am, p_bm); // (A-M)-(B-M)
    let padd_ambm = padd(d, p, p_am, p_bm); // (A-M)+(B-M)

    let fact_ab_point = {
        let neg_bx1 = cneg(d, p, bx);
        let ax_bx = cadd(d, p, ax, neg_bx1);
        let neg_bmx1 = cneg(d, p, bmx);
        let amx_bmx1 = cadd(d, p, amx, neg_bmx1);
        let claim_x = equiv(d, p, ax_bx, amx_bmx1);
        let neg_by1 = cneg(d, p, by);
        let ay_by = cadd(d, p, ay, neg_by1);
        let neg_bmy1 = cneg(d, p, bmy);
        let amy_bmy1 = cadd(d, p, amy, neg_bmy1);
        let claim_y = equiv(d, p, ay_by, amy_bmy1);
        and_intro(d, p, claim_x, claim_y, dd_ab_x, dd_ab_y)
    };
    let fact_ac_point = {
        let neg_cx1 = cneg(d, p, cx);
        let ax_cx1 = cadd(d, p, ax, neg_cx1);
        let amx_bmx2 = cadd(d, p, amx, bmx);
        let claim_x = equiv(d, p, ax_cx1, amx_bmx2);
        let neg_cy1 = cneg(d, p, cy);
        let ay_cy1 = cadd(d, p, ay, neg_cy1);
        let amy_bmy2 = cadd(d, p, amy, bmy);
        let claim_y = equiv(d, p, ay_cy1, amy_bmy2);
        and_intro(d, p, claim_x, claim_y, fact_ac_x, fact_ac_y)
    };

    // Expand distSq A B and distSq A C via dot_self_sub/dot_self_add at (P, D).
    let x_ = dotp(d, p, p_am, p_am);
    let y_ = dotp(d, p, p_am, p_bm);
    let z_ = dotp(d, p, p_bm, p_bm);

    let dot_abab = dotp(d, p, sub_ab, sub_ab);
    let dot_acac = dotp(d, p, sub_ac, sub_ac);
    let dot_ambm_ambm = dotp(d, p, psub_ambm, psub_ambm);
    let dot_pambm_pambm = dotp(d, p, padd_ambm, padd_ambm);

    let ab_congr = d.lemma(
        p.dot_congr,
        &[
            sub_ab,
            psub_ambm,
            sub_ab,
            psub_ambm,
            fact_ab_point,
            fact_ab_point,
        ],
    );
    let ab_expand = d.lemma(p.dot_self_sub, &[p_am, p_bm]); // Equiv(dot_ambm_ambm, term_sub)
    let ny = cneg(d, p, y_);
    let ny_z = cadd(d, p, ny, z_);
    let a_ = cadd(d, p, ny, ny_z);
    let term_sub = cadd(d, p, x_, a_);
    let ab_total = chain(
        d,
        p,
        dot_abab,
        &[(dot_ambm_ambm, ab_congr), (term_sub, ab_expand)],
    );

    let ac_congr = d.lemma(
        p.dot_congr,
        &[
            sub_ac,
            padd_ambm,
            sub_ac,
            padd_ambm,
            fact_ac_point,
            fact_ac_point,
        ],
    );
    let ac_expand = d.lemma(p.dot_self_add, &[p_am, p_bm]); // Equiv(dot_pambm_pambm, term_add)
    let y_z = cadd(d, p, y_, z_);
    let b_ = cadd(d, p, y_, y_z);
    let term_add = cadd(d, p, x_, b_);
    let ac_total = chain(
        d,
        p,
        dot_acac,
        &[(dot_pambm_pambm, ac_congr), (term_add, ac_expand)],
    );

    // Sum and combine.
    let s_raw = cadd(d, p, dot_abab, dot_acac);
    let s_congr = d.lemma(
        creal.add_congr,
        &[dot_abab, term_sub, dot_acac, term_add, ab_total, ac_total],
    );
    let combine_lhs = cadd(d, p, term_sub, term_add);
    let combine_result = apollonius_combine_proof(d, p, x_, y_, z_);
    let xx = cadd(d, p, x_, x_);
    let zz = cadd(d, p, z_, z_);
    let target = cadd(d, p, xx, zz);
    let final_proof = chain(
        d,
        p,
        s_raw,
        &[(combine_lhs, s_congr), (target, combine_result)],
    );

    let dsq_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dsq_ac = d.const_app(p.dist_sq, &[pa, pc]);
    let dsq_am = d.const_app(p.dist_sq, &[pa, pm]);
    let dsq_bm = d.const_app(p.dist_sq, &[pb, pm]);
    let s_named = cadd(d, p, dsq_ab, dsq_ac);
    let am_am = cadd(d, p, dsq_am, dsq_am);
    let bm_bm = cadd(d, p, dsq_bm, dsq_bm);
    let t_named = cadd(d, p, am_am, bm_bm);

    let ty_body = equiv(d, p, s_named, t_named);
    let ty = {
        let w2 = d.pi_fv(c_fv, point, ty_body);
        let w1 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(a_fv, point, w1)
    };
    let value = {
        let w2 = d.lam_fv(c_fv, point, final_proof);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.apollonius_median,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the centroid, `2/3` of the way along each median ----------------------

/// `Scalar.three := CReal.add two one`, and `threePosBound : PosBound three
/// 0`. Mirrors [`declare_two`] one level up: `le two three` is the same
/// `le_add_of_nonneg` step anchored at `two` instead of `one`, and `le_trans`
/// composes it with `two`'s own `le one two` bound into `le one three`, which
/// is `PosBound three 0` by definition (`natDivSucc 1 0 = 1`).
fn declare_three(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);

    let two_a = d.kernel().const_(p.two, vec![]);
    let one_a = d.kernel().const_(creal.one, vec![]);
    let three_value = cadd(d, p, two_a, one_a);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.three,
        uparams: vec![],
        ty: carrier,
        value: three_value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 9),
    })?;

    let rat = creal.rat;
    let rat_zero = d.kernel().const_(rat.zero, vec![]);
    let rat_one = d.kernel().const_(rat.one, vec![]);
    let strict = d.lemma(rat.zero_lt_one, &[]);
    let nonneg = d.lemma(rat.le_of_lt, &[rat_zero, rat_one, strict]);
    let two_b = d.kernel().const_(p.two, vec![]);
    // le two three, the same `le_add_of_nonneg` step `declare_two` runs at
    // `one` instead, now anchored at `two`.
    let le_two_three = d.lemma(creal.le_add_of_nonneg, &[two_b, rat_one, nonneg]);
    let one_b = d.kernel().const_(creal.one, vec![]);
    let two_c = d.kernel().const_(p.two, vec![]);
    let three_c = d.kernel().const_(p.three, vec![]);
    // `two_pos_bound : PosBound two 0`, used here at its defeq-unfolded type
    // `le one two` (exactly as `PosBound two 0` itself was admitted via a
    // `le`-typed proof value in `declare_two`).
    let le_one_two = d.kernel().const_(p.two_pos_bound, vec![]);
    let proof = d.lemma(
        creal.le_trans,
        &[one_b, two_c, three_c, le_one_two, le_two_three],
    );
    let three_const = d.kernel().const_(p.three, vec![]);
    let zero_nat = d.num(0);
    let ty = d.const_app(creal.pos_bound, &[three_const, zero_nat]);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.three_pos_bound,
        uparams: vec![],
        ty,
        value: proof,
    })
}

/// `Scalar.inv3 := CReal.inv three 0 threePosBound` — division by three.
fn declare_inv3(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);
    let three_const = d.kernel().const_(p.three, vec![]);
    let zero_nat = d.num(0);
    let h = d.kernel().const_(p.three_pos_bound, vec![]);
    let value = d.const_app(creal.inv, &[three_const, zero_nat, h]);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.inv3,
        uparams: vec![],
        ty: carrier,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 10),
    })
}

/// `CPoint.Scalar.centroid a b c := CReal.mul inv3 (CReal.add a (CReal.add b c))`.
fn declare_centroid_scalar(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let body = ccentroid_raw(d, p, a, b, c);

    let value = {
        let w3 = d.lam_fv(c_fv, carrier, body);
        let w2 = d.lam_fv(b_fv, carrier, w3);
        d.lam_fv(a_fv, carrier, w2)
    };
    let ty = {
        let w3 = d.arrow(carrier, carrier);
        let w2 = d.arrow(carrier, w3);
        d.arrow(carrier, w2)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.centroid_scalar,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 11),
    })
}

/// `CPoint.Scalar.centroid a b c` — the named constant application, used only
/// when stating a final theorem's type (mirrors [`midpoint`]); every proof
/// helper builds the same term in raw `mul`/`add` form instead
/// ([`ccentroid_raw`]), relying on the two being definitionally equal.
fn scalar_centroid(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    d.const_app(p.centroid_scalar, &[a, b, c])
}

/// `Scalar.centroid_self : ∀ a, Equiv (centroid a a a) a` — the discrimination
/// witness for `centroid`/`inv3`, mirroring [`declare_midpoint_self`] exactly
/// one level up (`three`/`inv3` in place of `two`/`inv2`, `(a+a)+a ~ a+(a+a)`
/// bridged by one extra `add_assoc` step to match `centroid`'s own
/// right-associated `a+(b+c)` argument shape).
fn declare_centroid_scalar_self(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let three = d.kernel().const_(p.three, vec![]);
    let inv3 = d.kernel().const_(p.inv3, vec![]);
    let aa = cadd(d, p, a, a);
    let s = cadd(d, p, a, aa); // a+(a+a)
    let g = cmul(d, p, inv3, s); // =defeq= centroid_scalar a a a

    // TA: mul three a ~ (a+a)+a ~ a+(a+a) = s
    let ta = three_mul_eq_triple_proof(d, p, a); // Equiv(mul three a, (a+a)+a)
    let aa_a = cadd(d, p, aa, a);
    let assoc_a = d.lemma(creal.add_assoc, &[a, a, a]); // Equiv(aa_a, s)
    let mul_three_a = cmul(d, p, three, a);
    let ta_s = chain(d, p, mul_three_a, &[(aa_a, ta), (s, assoc_a)]); // Equiv(mul_three_a, s)

    // INV3_THREE_ONE : mul inv3 three ~ one
    let three_inv3 = cmul(d, p, three, inv3);
    let inv3_three = cmul(d, p, inv3, three);
    let comm_step = d.lemma(creal.mul_comm, &[inv3, three]); // Equiv(inv3_three, three_inv3)
    let zero_nat = d.num(0);
    let h_three = d.kernel().const_(p.three_pos_bound, vec![]);
    let cancel = d.lemma(creal.mul_inv_cancel, &[three, zero_nat, h_three]); // Equiv(three_inv3, one)
    let one = d.kernel().const_(creal.one, vec![]);
    let inv3_three_one = chain(d, p, inv3_three, &[(three_inv3, comm_step), (one, cancel)]);

    // inv3 undoes mul by three: mul inv3 (mul three a) ~ a
    let inv3_three_a = cmul(d, p, inv3_three, a);
    let inv3_mul_three_a = cmul(d, p, inv3, mul_three_a);
    let assoc = d.lemma(creal.mul_assoc, &[inv3, three, a]); // Equiv(inv3_three_a, inv3_mul_three_a)
    let assoc_symm = symm(d, p, inv3_three_a, inv3_mul_three_a, assoc);
    let refl_a2 = refl(d, p, a);
    let congr1 = d.lemma(
        creal.mul_congr,
        &[inv3_three, one, a, a, inv3_three_one, refl_a2],
    );
    let mul_one_a_term = cmul(d, p, one, a);
    let mc = d.lemma(creal.mul_comm, &[one, a]);
    let moa = d.lemma(creal.mul_one, &[a]);
    let mul_a_one = cmul(d, p, a, one);
    let one_mul_a = chain(d, p, mul_one_a_term, &[(mul_a_one, mc), (a, moa)]);

    let inv3_undoes = chain(
        d,
        p,
        inv3_mul_three_a,
        &[
            (inv3_three_a, assoc_symm),
            (mul_one_a_term, congr1),
            (a, one_mul_a),
        ],
    );

    // meet: g = mul inv3 s ~ mul inv3 (mul three a) ~ a
    let ta_s_symm = symm(d, p, mul_three_a, s, ta_s);
    let refl_inv3 = refl(d, p, inv3);
    let congr2 = d.lemma(
        creal.mul_congr,
        &[inv3, inv3, s, mul_three_a, refl_inv3, ta_s_symm],
    );
    let final_proof = chain(d, p, g, &[(inv3_mul_three_a, congr2), (a, inv3_undoes)]);

    let scalar_centroid_aaa = scalar_centroid(d, p, a, a, a);
    let ty_body = equiv(d, p, scalar_centroid_aaa, a);
    let ty = d.pi_fv(a_fv, carrier, ty_body);
    let value = d.lam_fv(a_fv, carrier, final_proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.centroid_scalar_self,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.centroid A B C := CPoint.mk (Scalar.centroid (x A) (x B) (x C))
/// (Scalar.centroid (y A) (y B) (y C))`.
fn declare_centroid(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

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
    let gx = scalar_centroid(d, p, ax, bx, cx);
    let gy = scalar_centroid(d, p, ay, by, cy);
    let value_body = d.const_app(p.mk, &[gx, gy]);

    let value = {
        let w3 = d.lam_fv(c_fv, point, value_body);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    let ty = {
        let w3 = d.arrow(point, point);
        let w2 = d.arrow(point, w3);
        d.arrow(point, w2)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.centroid,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 12),
    })
}

/// **The centroid divides each median, additive form.** See
/// [`CPointPrelude::centroid_median`].
fn declare_centroid_median(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

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

    let proof_x = centroid_median_scalar_proof(d, p, ax, bx, cx);
    let proof_y = centroid_median_scalar_proof(d, p, ay, by, cy);

    // Claim types, in the SAME raw form the scalar proofs conclude with.
    let gx = ccentroid_raw(d, p, ax, bx, cx);
    let gy = ccentroid_raw(d, p, ay, by, cy);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let bcx = cadd(d, p, bx, cx);
    let mx = cmul(d, p, inv2, bcx);
    let bcy = cadd(d, p, by, cy);
    let my = cmul(d, p, inv2, bcy);

    let claim_x = {
        let gg = cadd(d, p, gx, gx);
        let gg_g = cadd(d, p, gg, gx);
        let mm = cadd(d, p, mx, mx);
        let a_mm = cadd(d, p, ax, mm);
        equiv(d, p, gg_g, a_mm)
    };
    let claim_y = {
        let gg = cadd(d, p, gy, gy);
        let gg_g = cadd(d, p, gg, gy);
        let mm = cadd(d, p, my, my);
        let a_mm = cadd(d, p, ay, mm);
        equiv(d, p, gg_g, a_mm)
    };
    let proof = and_intro(d, p, claim_x, claim_y, proof_x, proof_y);

    let big_g = d.const_app(p.centroid, &[pa, pb, pc]);
    let big_m = d.const_app(p.point_midpoint, &[pb, pc]);
    let gg_point = padd(d, p, big_g, big_g);
    let ggg_point = padd(d, p, gg_point, big_g);
    let mm_point = padd(d, p, big_m, big_m);
    let a_mm_point = padd(d, p, pa, mm_point);
    let ty_body = d.const_app(p.point_equiv, &[ggg_point, a_mm_point]);

    let ty = {
        let w2 = d.pi_fv(c_fv, point, ty_body);
        let w1 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(a_fv, point, w1)
    };
    let value = {
        let w2 = d.lam_fv(c_fv, point, proof);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.centroid_median,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Leibniz's centroid formula, unconditional.** See
/// [`CPointPrelude::centroid_dist_sq`].
///
/// Writing `G := centroid A B C`, `u := P-G`, `a_ := A-G`, `b_ := B-G`,
/// `c_ := C-G`: `distSq P X` for each vertex `X` expands via
/// [`Self::dot_self_sub`] applied at `(u, X_)` into a four-term sum in
/// `dot u u`, `dot u X_` (twice, negated), `dot X_ X_`. Summing the three
/// gives twelve terms; six of them (`dot u a_`, `dot u b_`, `dot u c_`, each
/// twice) cancel because `a_+b_+c_ ~ 0` — exactly `3G ~ A+B+C` rearranged
/// ([`triple_g_eq_sum_add_form_proof`] + [`triple_sub_sum_zero_proof`] +
/// [`dot_zero_right_proof`]) — leaving `3·dot u u + (dot a_ a_ + dot b_ b_ +
/// dot c_ c_)`, i.e. `3·distSq P G + (distSq G A + distSq G B + distSq G C)`
/// after three `dist_sq_comm` flips. The twelve-term bookkeeping is the
/// generic `SumTree`/`flatten_sum_tree`/`reorder_right_chain`/
/// `concat_right_chains` machinery, reused rather than hand-derived.
fn declare_centroid_dist_sq(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv); // P
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv); // A
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv); // B
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv); // C

    let px = d.const_app(p.x, &[pp]);
    let py = d.const_app(p.y, &[pp]);
    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);

    let gx = ccentroid_raw(d, p, ax, bx, cx);
    let gy = ccentroid_raw(d, p, ay, by, cy);
    let big_g = d.const_app(p.mk, &[gx, gy]); // raw =defeq= centroid A B C

    let u_pt = psub(d, p, pp, big_g);
    let a_pt = psub(d, p, pa, big_g);
    let b_pt = psub(d, p, pb, big_g);
    let c_pt = psub(d, p, pc, big_g);

    let neg_gx = cneg(d, p, gx);
    let neg_gy = cneg(d, p, gy);
    let ux = cadd(d, p, px, neg_gx);
    let uy = cadd(d, p, py, neg_gy);
    let ax_ = cadd(d, p, ax, neg_gx);
    let ay_ = cadd(d, p, ay, neg_gy);
    let bx_ = cadd(d, p, bx, neg_gx);
    let by_ = cadd(d, p, by, neg_gy);
    let cx_ = cadd(d, p, cx, neg_gx);
    let cy_ = cadd(d, p, cy, neg_gy);

    // P - X ~ (P-G) - (X-G), per coordinate, for X in {A,B,C}.
    let dd_pa_x = diff_diff_scalar_proof(d, p, px, ax, gx);
    let dd_pa_y = diff_diff_scalar_proof(d, p, py, ay, gy);
    let dd_pb_x = diff_diff_scalar_proof(d, p, px, bx, gx);
    let dd_pb_y = diff_diff_scalar_proof(d, p, py, by, gy);
    let dd_pc_x = diff_diff_scalar_proof(d, p, px, cx, gx);
    let dd_pc_y = diff_diff_scalar_proof(d, p, py, cy, gy);

    let fact_pa_point = {
        let neg_ax = cneg(d, p, ax);
        let neg_ax_ = cneg(d, p, ax_);
        let neg_ay = cneg(d, p, ay);
        let neg_ay_ = cneg(d, p, ay_);
        let lhs_x = cadd(d, p, px, neg_ax);
        let rhs_x = cadd(d, p, ux, neg_ax_);
        let lhs_y = cadd(d, p, py, neg_ay);
        let rhs_y = cadd(d, p, uy, neg_ay_);
        let claim_x = equiv(d, p, lhs_x, rhs_x);
        let claim_y = equiv(d, p, lhs_y, rhs_y);
        and_intro(d, p, claim_x, claim_y, dd_pa_x, dd_pa_y)
    };
    let fact_pb_point = {
        let neg_bx = cneg(d, p, bx);
        let neg_bx_ = cneg(d, p, bx_);
        let neg_by = cneg(d, p, by);
        let neg_by_ = cneg(d, p, by_);
        let lhs_x = cadd(d, p, px, neg_bx);
        let rhs_x = cadd(d, p, ux, neg_bx_);
        let lhs_y = cadd(d, p, py, neg_by);
        let rhs_y = cadd(d, p, uy, neg_by_);
        let claim_x = equiv(d, p, lhs_x, rhs_x);
        let claim_y = equiv(d, p, lhs_y, rhs_y);
        and_intro(d, p, claim_x, claim_y, dd_pb_x, dd_pb_y)
    };
    let fact_pc_point = {
        let neg_cx = cneg(d, p, cx);
        let neg_cx_ = cneg(d, p, cx_);
        let neg_cy = cneg(d, p, cy);
        let neg_cy_ = cneg(d, p, cy_);
        let lhs_x = cadd(d, p, px, neg_cx);
        let rhs_x = cadd(d, p, ux, neg_cx_);
        let lhs_y = cadd(d, p, py, neg_cy);
        let rhs_y = cadd(d, p, uy, neg_cy_);
        let claim_x = equiv(d, p, lhs_x, rhs_x);
        let claim_y = equiv(d, p, lhs_y, rhs_y);
        and_intro(d, p, claim_x, claim_y, dd_pc_x, dd_pc_y)
    };

    let sub_pa = psub(d, p, pp, pa);
    let sub_pb = psub(d, p, pp, pb);
    let sub_pc = psub(d, p, pp, pc);
    let psub_u_a = psub(d, p, u_pt, a_pt);
    let psub_u_b = psub(d, p, u_pt, b_pt);
    let psub_u_c = psub(d, p, u_pt, c_pt);

    let dot_pa_pa = dotp(d, p, sub_pa, sub_pa);
    let dot_ua_ua = dotp(d, p, psub_u_a, psub_u_a);
    let pa_congr = d.lemma(
        p.dot_congr,
        &[
            sub_pa,
            psub_u_a,
            sub_pa,
            psub_u_a,
            fact_pa_point,
            fact_pa_point,
        ],
    );
    let pa_expand = d.lemma(p.dot_self_sub, &[u_pt, a_pt]);

    let dot_pb_pb = dotp(d, p, sub_pb, sub_pb);
    let dot_ub_ub = dotp(d, p, psub_u_b, psub_u_b);
    let pb_congr = d.lemma(
        p.dot_congr,
        &[
            sub_pb,
            psub_u_b,
            sub_pb,
            psub_u_b,
            fact_pb_point,
            fact_pb_point,
        ],
    );
    let pb_expand = d.lemma(p.dot_self_sub, &[u_pt, b_pt]);

    let dot_pc_pc = dotp(d, p, sub_pc, sub_pc);
    let dot_uc_uc = dotp(d, p, psub_u_c, psub_u_c);
    let pc_congr = d.lemma(
        p.dot_congr,
        &[
            sub_pc,
            psub_u_c,
            sub_pc,
            psub_u_c,
            fact_pc_point,
            fact_pc_point,
        ],
    );
    let pc_expand = d.lemma(p.dot_self_sub, &[u_pt, c_pt]);

    // The atomic leaves.
    let uu = dotp(d, p, u_pt, u_pt);
    let ua = dotp(d, p, u_pt, a_pt);
    let ub = dotp(d, p, u_pt, b_pt);
    let uc = dotp(d, p, u_pt, c_pt);
    let aa = dotp(d, p, a_pt, a_pt);
    let bb = dotp(d, p, b_pt, b_pt);
    let cc = dotp(d, p, c_pt, c_pt);
    let nua = cneg(d, p, ua);
    let nub = cneg(d, p, ub);
    let nuc = cneg(d, p, uc);

    let term_pa_tree = sadd(
        SumTree::Leaf(uu),
        sadd(
            SumTree::Leaf(nua),
            sadd(SumTree::Leaf(nua), SumTree::Leaf(aa)),
        ),
    );
    let term_pb_tree = sadd(
        SumTree::Leaf(uu),
        sadd(
            SumTree::Leaf(nub),
            sadd(SumTree::Leaf(nub), SumTree::Leaf(bb)),
        ),
    );
    let term_pc_tree = sadd(
        SumTree::Leaf(uu),
        sadd(
            SumTree::Leaf(nuc),
            sadd(SumTree::Leaf(nuc), SumTree::Leaf(cc)),
        ),
    );
    let term_pa_expr = sum_tree_build(d, p, &term_pa_tree);
    let term_pb_expr = sum_tree_build(d, p, &term_pb_tree);
    let term_pc_expr = sum_tree_build(d, p, &term_pc_tree);

    let pa_total = chain(
        d,
        p,
        dot_pa_pa,
        &[(dot_ua_ua, pa_congr), (term_pa_expr, pa_expand)],
    );
    let pb_total = chain(
        d,
        p,
        dot_pb_pb,
        &[(dot_ub_ub, pb_congr), (term_pb_expr, pb_expand)],
    );
    let pc_total = chain(
        d,
        p,
        dot_pc_pc,
        &[(dot_uc_uc, pc_congr), (term_pc_expr, pc_expand)],
    );

    // S_raw := distSq(P,A) + (distSq(P,B) + distSq(P,C)) ~ term_pa + (term_pb + term_pc)
    let dot_pb_pc = cadd(d, p, dot_pb_pb, dot_pc_pc);
    let term_pb_pc = cadd(d, p, term_pb_expr, term_pc_expr);
    let congr_bc = d.lemma(
        creal.add_congr,
        &[
            dot_pb_pb,
            term_pb_expr,
            dot_pc_pc,
            term_pc_expr,
            pb_total,
            pc_total,
        ],
    );
    let s_raw = cadd(d, p, dot_pa_pa, dot_pb_pc);
    let s_expanded = cadd(d, p, term_pa_expr, term_pb_pc);
    let congr_all = d.lemma(
        creal.add_congr,
        &[
            dot_pa_pa,
            term_pa_expr,
            dot_pb_pc,
            term_pb_pc,
            pa_total,
            congr_bc,
        ],
    );

    let s_tree = sadd(
        term_pa_tree.clone(),
        sadd(term_pb_tree.clone(), term_pc_tree.clone()),
    );
    let (s_chain, s_flatten) = flatten_sum_tree(d, p, &s_tree); // Equiv(s_expanded, s_chain)

    let mut s_leaves = Vec::new();
    sum_tree_leaves(&s_tree, &mut s_leaves); // [uu,nua,nua,aa, uu,nub,nub,bb, uu,nuc,nuc,cc]
    let to_leaves = vec![nua, nub, nuc, nua, nub, nuc, uu, uu, uu, aa, bb, cc];
    let reorder = reorder_right_chain(d, p, &s_leaves, &to_leaves); // Equiv(s_chain, to_chain)
    let to_chain = build_right_chain(d, p, &to_leaves);

    // Split into the 6 cancelling leaves and the 6 surviving leaves.
    let keep_chain = build_right_chain(d, p, &[uu, uu, uu, aa, bb, cc]);
    let cancel_chain = build_right_chain(d, p, &[nua, nub, nuc, nua, nub, nuc]);
    let (outer_result, outer_proof) =
        concat_right_chains(d, p, &[nua, nub, nuc, nua, nub, nuc], keep_chain);
    // outer_proof : Equiv(add cancel_chain keep_chain, outer_result); outer_result =defeq= to_chain.
    let cancel_keep_raw = cadd(d, p, cancel_chain, keep_chain);
    let outer_split = symm(d, p, cancel_keep_raw, outer_result, outer_proof); // Equiv(outer_result, add cancel_chain keep_chain)

    // cancel_chain ~ abc3_chain + abc3_chain, where abc3_chain := nua+(nub+nuc).
    let abc3_chain = build_right_chain(d, p, &[nua, nub, nuc]);
    let (cancel_result, cancel_proof) = concat_right_chains(d, p, &[nua, nub, nuc], abc3_chain);
    // cancel_proof : Equiv(add abc3_chain abc3_chain, cancel_result); cancel_result =defeq= cancel_chain.
    let abc3_abc3_raw = cadd(d, p, abc3_chain, abc3_chain);
    let cancel_split = symm(d, p, abc3_abc3_raw, cancel_result, cancel_proof); // Equiv(cancel_result, add abc3_chain abc3_chain)

    // abc3_chain ~ 0, via the cross-term-zero fact: ua+(ub+uc) ~ 0.
    let uc_add = cadd(d, p, ub, uc);
    let s3 = cadd(d, p, ua, uc_add); // ua + (ub+uc)

    let padd_bc = padd(d, p, b_pt, c_pt);
    let padd_abc = padd(d, p, a_pt, padd_bc);
    let dot_u_padd_bc = dotp(d, p, u_pt, padd_bc);
    let dot_u_sum = dotp(d, p, u_pt, padd_abc);

    let dar1 = d.lemma(p.dot_add_right, &[u_pt, b_pt, c_pt]); // Equiv(dot_u_padd_bc, ub+uc)
    let dar1_symm = symm(d, p, dot_u_padd_bc, uc_add, dar1); // Equiv(uc_add, dot_u_padd_bc)
    let refl_ua = refl(d, p, ua);
    let ua_plus = cadd(d, p, ua, dot_u_padd_bc);
    let congr_s3a = d.lemma(
        creal.add_congr,
        &[ua, ua, uc_add, dot_u_padd_bc, refl_ua, dar1_symm],
    ); // Equiv(s3, ua_plus)

    let dar2 = d.lemma(p.dot_add_right, &[u_pt, a_pt, padd_bc]); // Equiv(dot_u_sum, ua_plus)
    let dar2_symm = symm(d, p, dot_u_sum, ua_plus, dar2); // Equiv(ua_plus, dot_u_sum)

    let s3_to_dot = chain(d, p, s3, &[(ua_plus, congr_s3a), (dot_u_sum, dar2_symm)]); // Equiv(s3, dot_u_sum)

    // padd_abc ~ zero_point, per coordinate.
    let hgx = triple_g_eq_sum_add_form_proof(d, p, ax, bx, cx); // Equiv(gx+(gx+gx), ax+(bx+cx))
    let hgy = triple_g_eq_sum_add_form_proof(d, p, ay, by, cy);
    let tsx = triple_sub_sum_zero_proof(d, p, ax, bx, cx, gx, hgx);
    let tsy = triple_sub_sum_zero_proof(d, p, ay, by, cy, gy, hgy);

    let zero = czero(d, p);
    let claim_zx = {
        let ngx = cneg(d, p, gx);
        let a_ngx = cadd(d, p, ax, ngx);
        let b_ngx = cadd(d, p, bx, ngx);
        let c_ngx = cadd(d, p, cx, ngx);
        let bc_ngx = cadd(d, p, b_ngx, c_ngx);
        let lhs_x = cadd(d, p, a_ngx, bc_ngx);
        equiv(d, p, lhs_x, zero)
    };
    let claim_zy = {
        let ngy = cneg(d, p, gy);
        let a_ngy = cadd(d, p, ay, ngy);
        let b_ngy = cadd(d, p, by, ngy);
        let c_ngy = cadd(d, p, cy, ngy);
        let bc_ngy = cadd(d, p, b_ngy, c_ngy);
        let lhs_y = cadd(d, p, a_ngy, bc_ngy);
        equiv(d, p, lhs_y, zero)
    };
    let fact_zero_point = and_intro(d, p, claim_zx, claim_zy, tsx, tsy); // CPoint.Equiv(padd_abc, zero_point), defeq

    let zero_point = d.const_app(p.mk, &[zero, zero]);
    let refl_u_point = point_equiv_refl(d, p, u_pt);
    let dot_u_zp = dotp(d, p, u_pt, zero_point);
    let dot_congr_zero = d.lemma(
        p.dot_congr,
        &[
            u_pt,
            u_pt,
            padd_abc,
            zero_point,
            refl_u_point,
            fact_zero_point,
        ],
    ); // Equiv(dot_u_sum, dot_u_zp)
    let dzr = dot_zero_right_proof(d, p, u_pt); // Equiv(dot_u_zp, zero)

    let crosszero_raw = chain(
        d,
        p,
        s3,
        &[
            (dot_u_sum, s3_to_dot),
            (dot_u_zp, dot_congr_zero),
            (zero, dzr),
        ],
    ); // Equiv(s3, zero)

    // abc3_chain ~ neg(s3) ~ zero.
    let na_step_bc = neg_add_proof(d, p, ub, uc); // Equiv(neg(uc_add), nub+nuc)
    let nub_nuc = cadd(d, p, nub, nuc);
    let neg_uc_add = cneg(d, p, uc_add);
    let na_step_bc_symm = symm(d, p, neg_uc_add, nub_nuc, na_step_bc); // Equiv(nub_nuc, neg_uc_add)
    let refl_nua = refl(d, p, nua);
    let nua_plus_neg = cadd(d, p, nua, neg_uc_add);
    let congr_abc3 = d.lemma(
        creal.add_congr,
        &[nua, nua, nub_nuc, neg_uc_add, refl_nua, na_step_bc_symm],
    ); // Equiv(abc3_chain, nua_plus_neg)

    let neg_s3 = cneg(d, p, s3);
    let na_step_a = neg_add_proof(d, p, ua, uc_add); // Equiv(neg_s3, nua_plus_neg)
    let na_step_a_symm = symm(d, p, neg_s3, nua_plus_neg, na_step_a); // Equiv(nua_plus_neg, neg_s3)

    let neg_congr_cz = d.lemma(creal.neg_congr, &[s3, zero, crosszero_raw]); // Equiv(neg_s3, neg zero)
    let neg_zero = cneg(d, p, zero);
    let nz_proof = neg_zero_proof(d, p); // Equiv(neg_zero, zero)
    let neg_s3_to_zero = chain(d, p, neg_s3, &[(neg_zero, neg_congr_cz), (zero, nz_proof)]); // Equiv(neg_s3, zero)

    let abc3_to_zero = chain(
        d,
        p,
        abc3_chain,
        &[
            (nua_plus_neg, congr_abc3),
            (neg_s3, na_step_a_symm),
            (zero, neg_s3_to_zero),
        ],
    ); // Equiv(abc3_chain, zero)

    // cancel_chain ~ 0.
    let abc3_abc3 = cadd(d, p, abc3_chain, abc3_chain);
    let congr_cancel = d.lemma(
        creal.add_congr,
        &[
            abc3_chain,
            zero,
            abc3_chain,
            zero,
            abc3_to_zero,
            abc3_to_zero,
        ],
    ); // Equiv(abc3_abc3, zero+zero)
    let zero_zero = cadd(d, p, zero, zero);
    let az_zero = d.lemma(creal.add_zero, &[zero]); // Equiv(zero_zero, zero)
    let bridge_cancel_result = refl(d, p, cancel_result);
    let cancel_to_zero = chain(
        d,
        p,
        cancel_chain,
        &[
            (cancel_result, bridge_cancel_result),
            (abc3_abc3, cancel_split),
            (zero_zero, congr_cancel),
            (zero, az_zero),
        ],
    ); // Equiv(cancel_chain, zero)

    // to_chain ~ keep_chain.
    let cancel_keep = cadd(d, p, cancel_chain, keep_chain);
    let refl_keep = refl(d, p, keep_chain);
    let congr_zero_keep = d.lemma(
        creal.add_congr,
        &[
            cancel_chain,
            zero,
            keep_chain,
            keep_chain,
            cancel_to_zero,
            refl_keep,
        ],
    ); // Equiv(cancel_keep, zero+keep_chain)
    let zero_keep = cadd(d, p, zero, keep_chain);
    let za_keep = zero_add_proof(d, p, keep_chain); // Equiv(zero_keep, keep_chain)

    let bridge_outer_result = refl(d, p, outer_result);
    let to_chain_to_keep = chain(
        d,
        p,
        to_chain,
        &[
            (outer_result, bridge_outer_result),
            (cancel_keep, outer_split),
            (zero_keep, congr_zero_keep),
            (keep_chain, za_keep),
        ],
    ); // Equiv(to_chain, keep_chain)

    // keep_chain ~ (Uu+(Uu+Uu)) + (dsq(G,A)+(dsq(G,B)+dsq(G,C))).
    let uu3_chain = build_right_chain(d, p, &[uu, uu, uu]);
    let abc_final_chain = build_right_chain(d, p, &[aa, bb, cc]);
    let (keep_result, keep_proof) = concat_right_chains(d, p, &[uu, uu, uu], abc_final_chain);
    let uu3_abc_final_raw = cadd(d, p, uu3_chain, abc_final_chain);
    let keep_split = symm(d, p, uu3_abc_final_raw, keep_result, keep_proof); // Equiv(keep_result, uu3_chain+abc_final_chain)
    let uu3_abc_final = cadd(d, p, uu3_chain, abc_final_chain);
    let bridge_keep_result = refl(d, p, keep_result);
    let keep_to_split = chain(
        d,
        p,
        keep_chain,
        &[
            (keep_result, bridge_keep_result),
            (uu3_abc_final, keep_split),
        ],
    ); // Equiv(keep_chain, uu3_abc_final)

    let comm_a = d.lemma(p.dist_sq_comm, &[pa, big_g]); // Equiv(aa, dsq(G,A)), defeq
    let comm_b = d.lemma(p.dist_sq_comm, &[pb, big_g]);
    let comm_c = d.lemma(p.dist_sq_comm, &[pc, big_g]);
    let dsq_ga = d.const_app(p.dist_sq, &[big_g, pa]);
    let dsq_gb = d.const_app(p.dist_sq, &[big_g, pb]);
    let dsq_gc = d.const_app(p.dist_sq, &[big_g, pc]);
    let dsq_gb_gc = cadd(d, p, dsq_gb, dsq_gc);
    let congr_bc_final = d.lemma(creal.add_congr, &[bb, dsq_gb, cc, dsq_gc, comm_b, comm_c]);
    let bb_cc = cadd(d, p, bb, cc);
    let congr_abc_final = d.lemma(
        creal.add_congr,
        &[aa, dsq_ga, bb_cc, dsq_gb_gc, comm_a, congr_bc_final],
    ); // Equiv(abc_final_chain, dsq_ga_chain)
    let dsq_ga_chain = cadd(d, p, dsq_ga, dsq_gb_gc);
    let refl_uu3_chain = refl(d, p, uu3_chain);
    let congr_final_replace = d.lemma(
        creal.add_congr,
        &[
            uu3_chain,
            uu3_chain,
            abc_final_chain,
            dsq_ga_chain,
            refl_uu3_chain,
            congr_abc_final,
        ],
    ); // Equiv(uu3_abc_final, uu3_final)
    let uu3_final = cadd(d, p, uu3_chain, dsq_ga_chain);

    let final_proof = chain(
        d,
        p,
        s_raw,
        &[
            (s_expanded, congr_all),
            (s_chain, s_flatten),
            (to_chain, reorder),
            (keep_chain, to_chain_to_keep),
            (uu3_abc_final, keep_to_split),
            (uu3_final, congr_final_replace),
        ],
    );

    // State the theorem over `distSq`/`centroid`, defeq to the raw form above.
    let big_g_named = d.const_app(p.centroid, &[pa, pb, pc]);
    let dsq_pa_named = d.const_app(p.dist_sq, &[pp, pa]);
    let dsq_pb_named = d.const_app(p.dist_sq, &[pp, pb]);
    let dsq_pc_named = d.const_app(p.dist_sq, &[pp, pc]);
    let dsq_pb_pc_named = cadd(d, p, dsq_pb_named, dsq_pc_named);
    let s_named = cadd(d, p, dsq_pa_named, dsq_pb_pc_named);

    let dsq_pg_named = d.const_app(p.dist_sq, &[pp, big_g_named]);
    let dsq_pg_pg_named = cadd(d, p, dsq_pg_named, dsq_pg_named);
    let uu3_named = cadd(d, p, dsq_pg_named, dsq_pg_pg_named);
    let ga_named = d.const_app(p.dist_sq, &[big_g_named, pa]);
    let gb_named = d.const_app(p.dist_sq, &[big_g_named, pb]);
    let gc_named = d.const_app(p.dist_sq, &[big_g_named, pc]);
    let gb_gc_named = cadd(d, p, gb_named, gc_named);
    let abc_named = cadd(d, p, ga_named, gb_gc_named);
    let t_named = cadd(d, p, uu3_named, abc_named);

    let ty_body = equiv(d, p, s_named, t_named);
    let ty = {
        let w3 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w3);
        let w1 = d.pi_fv(a_fv, point, w2);
        d.pi_fv(pp_fv, point, w1)
    };
    let value = {
        let w3 = d.lam_fv(c_fv, point, final_proof);
        let w2 = d.lam_fv(b_fv, point, w3);
        let w1 = d.lam_fv(a_fv, point, w2);
        d.lam_fv(pp_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.centroid_dist_sq,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the cevian parametrisation: `lerp B C t := B + t·(C−B)` ---------------

/// Raw `add a (mul t (add b (neg a)))` — definitionally `Scalar.lerp a b t`,
/// built inline the way [`ccentroid_raw`] builds `Scalar.centroid`'s body, so
/// the scalar-level sanity proofs below can manipulate it syntactically
/// before `Scalar.lerp` itself is declared.
fn lerp_raw(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId, t: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let b_na = cadd(d, p, b, na);
    let t_b_na = cmul(d, p, t, b_na);
    cadd(d, p, a, t_b_na)
}

/// `Equiv (mul zero x) zero`.
fn zero_mul_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let mul_zero_x = cmul(d, p, zero, x);
    let mul_x_zero = cmul(d, p, x, zero);
    let comm = d.lemma(creal.mul_comm, &[zero, x]);
    let mz = d.lemma(creal.mul_zero, &[x]);
    chain(d, p, mul_zero_x, &[(mul_x_zero, comm), (zero, mz)])
}

/// `Equiv (mul one x) x`.
fn one_mul_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    let creal = p.creal;
    let one = d.kernel().const_(creal.one, vec![]);
    let mul_one_x = cmul(d, p, one, x);
    let mul_x_one = cmul(d, p, x, one);
    let comm = d.lemma(creal.mul_comm, &[one, x]);
    let mo = d.lemma(creal.mul_one, &[x]);
    chain(d, p, mul_one_x, &[(mul_x_one, comm), (x, mo)])
}

/// `Equiv (add a (add b (neg a))) b` — "add `a`, then walk back to `b`":
/// `a + (b − a) ~ b`.
fn add_cancel_middle_proof(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    let creal = p.creal;
    let na = cneg(d, p, a);
    let b_na = cadd(d, p, b, na);
    let lhs = cadd(d, p, a, b_na);

    let na_b = cadd(d, p, na, b);
    let comm1 = d.lemma(creal.add_comm, &[b, na]); // Equiv(b_na, na_b)
    let refl_a = refl(d, p, a);
    let a_na_b = cadd(d, p, a, na_b);
    let congr1 = d.lemma(creal.add_congr, &[a, a, b_na, na_b, refl_a, comm1]); // Equiv(lhs, a_na_b)

    let a_na = cadd(d, p, a, na);
    let a_na_then_b = cadd(d, p, a_na, b);
    let assoc = d.lemma(creal.add_assoc, &[a, na, b]); // Equiv(a_na_then_b, a_na_b)
    let assoc_symm = symm(d, p, a_na_then_b, a_na_b, assoc); // Equiv(a_na_b, a_na_then_b)

    let an = d.lemma(creal.add_neg, &[a]); // Equiv(a_na, zero)
    let zero = czero(d, p);
    let refl_b = refl(d, p, b);
    let congr2 = d.lemma(creal.add_congr, &[a_na, zero, b, b, an, refl_b]); // Equiv(a_na_then_b, zero_b)
    let zero_b = cadd(d, p, zero, b);
    let zb = zero_add_proof(d, p, b); // Equiv(zero_b, b)

    chain(
        d,
        p,
        lhs,
        &[
            (a_na_b, congr1),
            (a_na_then_b, assoc_symm),
            (zero_b, congr2),
            (b, zb),
        ],
    )
}

/// `Equiv (add inv2 inv2) one`.
fn inv2_double_one_proof(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let two = d.kernel().const_(p.two, vec![]);
    let zero_nat = d.num(0);
    let h_two = d.kernel().const_(p.two_pos_bound, vec![]);

    let double_fact = two_mul_eq_double_proof(d, p, inv2); // Equiv(mul two inv2, add inv2 inv2)
    let mul_two_inv2 = cmul(d, p, two, inv2);
    let inv2_inv2 = cadd(d, p, inv2, inv2);
    let double_symm = symm(d, p, mul_two_inv2, inv2_inv2, double_fact); // Equiv(inv2_inv2, mul_two_inv2)
    let cancel = d.lemma(creal.mul_inv_cancel, &[two, zero_nat, h_two]); // Equiv(mul_two_inv2, one)
    let one = d.kernel().const_(creal.one, vec![]);
    chain(
        d,
        p,
        inv2_inv2,
        &[(mul_two_inv2, double_symm), (one, cancel)],
    )
}

/// `Equiv a (add (mul inv2 a) (mul inv2 a))` — `a ~ ia + ia` where `ia := mul
/// inv2 a`. The discrimination content [`CPointPrelude::lerp_half_is_midpoint`]
/// needs: without `inv2 + inv2 ~ one`, this would not hold of `inv2`.
fn half_double_proof(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId) -> ExprId {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let one = d.kernel().const_(creal.one, vec![]);

    let mul_a_one = cmul(d, p, a, one);
    let mo = d.lemma(creal.mul_one, &[a]); // Equiv(mul_a_one, a)
    let mo_symm = symm(d, p, mul_a_one, a, mo); // Equiv(a, mul_a_one)

    let inv2_inv2 = cadd(d, p, inv2, inv2);
    let double_one = inv2_double_one_proof(d, p); // Equiv(inv2_inv2, one)
    let double_one_symm = symm(d, p, inv2_inv2, one, double_one); // Equiv(one, inv2_inv2)
    let refl_a = refl(d, p, a);
    let mul_a_inv2inv2 = cmul(d, p, a, inv2_inv2);
    let congr1 = d.lemma(
        creal.mul_congr,
        &[a, a, one, inv2_inv2, refl_a, double_one_symm],
    ); // Equiv(mul_a_one, mul_a_inv2inv2)

    let mul_a_inv2_1 = cmul(d, p, a, inv2);
    let mul_a_inv2_2 = cmul(d, p, a, inv2);
    let sum_mul_a_inv2 = cadd(d, p, mul_a_inv2_1, mul_a_inv2_2);
    let ld = d.lemma(creal.left_distrib, &[a, inv2, inv2]); // Equiv(mul_a_inv2inv2, sum_mul_a_inv2)

    let ia = cmul(d, p, inv2, a);
    let comm1 = d.lemma(creal.mul_comm, &[a, inv2]); // Equiv(mul_a_inv2_1, ia)
    let comm2 = d.lemma(creal.mul_comm, &[a, inv2]); // Equiv(mul_a_inv2_2, ia)
    let ia_ia = cadd(d, p, ia, ia);
    let congr2 = d.lemma(
        creal.add_congr,
        &[mul_a_inv2_1, ia, mul_a_inv2_2, ia, comm1, comm2],
    ); // Equiv(sum_mul_a_inv2, ia_ia)

    chain(
        d,
        p,
        a,
        &[
            (mul_a_one, mo_symm),
            (mul_a_inv2inv2, congr1),
            (sum_mul_a_inv2, ld),
            (ia_ia, congr2),
        ],
    )
}

/// `Equiv (mul x (mul t y)) (mul t (mul x y))` — pulling a left scalar factor
/// out from under another product: `x·(t·y) ~ t·(x·y)`.
fn mul_left_swap_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    t: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ty_ = cmul(d, p, t, y);
    let x_ty = cmul(d, p, x, ty_);

    let xt = cmul(d, p, x, t);
    let xt_y = cmul(d, p, xt, y);
    let assoc = d.lemma(creal.mul_assoc, &[x, t, y]); // Equiv(xt_y, x_ty)
    let assoc_symm = symm(d, p, xt_y, x_ty, assoc); // Equiv(x_ty, xt_y)

    let tx = cmul(d, p, t, x);
    let tx_y = cmul(d, p, tx, y);
    let comm_xt = d.lemma(creal.mul_comm, &[x, t]); // Equiv(xt, tx)
    let refl_y = refl(d, p, y);
    let congr1 = d.lemma(creal.mul_congr, &[xt, tx, y, y, comm_xt, refl_y]); // Equiv(xt_y, tx_y)

    let xy = cmul(d, p, x, y);
    let t_xy = cmul(d, p, t, xy);
    let assoc2 = d.lemma(creal.mul_assoc, &[t, x, y]); // Equiv(tx_y, t_xy)

    chain(
        d,
        p,
        x_ty,
        &[(xt_y, assoc_symm), (tx_y, congr1), (t_xy, assoc2)],
    )
}

/// `Equiv (mul (mul t x) (mul t x)) (mul t (mul t (mul x x)))` —
/// `(t·x)² ~ t·(t·x²)`, the "scalar squared pulls all the way out" fact
/// [`CPointPrelude::lerp_dist_sq`]'s `t²·distSq B C` coefficient needs.
fn sq_scale_proof(d: &mut IntDev<'_>, p: CPointPrelude, t: ExprId, x: ExprId) -> ExprId {
    let creal = p.creal;
    let tx = cmul(d, p, t, x);
    let sq = cmul(d, p, tx, tx);

    // sq ~ t*(tx*x)   [mul_left_swap_proof(t, tx, x), since `mul t x` = tx]
    let step_a = mul_left_swap_proof(d, p, t, tx, x);
    let tx_x = cmul(d, p, tx, x);
    let t_txx = cmul(d, p, t, tx_x);

    // tx*x ~ t*(x*x)
    let x_tx = cmul(d, p, x, tx);
    let comm1 = d.lemma(creal.mul_comm, &[tx, x]); // Equiv(tx_x, x_tx)
    let xx = cmul(d, p, x, x);
    let t_xx = cmul(d, p, t, xx);
    let step_b2 = mul_left_swap_proof(d, p, t, x, x); // Equiv(x_tx, t_xx)
    let txx_reduce = chain(d, p, tx_x, &[(x_tx, comm1), (t_xx, step_b2)]);

    let refl_t = refl(d, p, t);
    let congr_c = d.lemma(creal.mul_congr, &[t, t, tx_x, t_xx, refl_t, txx_reduce]);
    let t_t_xx = cmul(d, p, t, t_xx);

    chain(d, p, sq, &[(t_txx, step_a), (t_t_xx, congr_c)])
}

/// `Equiv (lerp_raw a b zero) a`.
fn lerp_scalar_zero_proof(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let na = cneg(d, p, a);
    let b_na = cadd(d, p, b, na);
    let mul_zero_bna = cmul(d, p, zero, b_na);
    let lhs = cadd(d, p, a, mul_zero_bna);

    let zm = zero_mul_proof(d, p, b_na); // Equiv(mul_zero_bna, zero)
    let refl_a = refl(d, p, a);
    let congr = d.lemma(creal.add_congr, &[a, a, mul_zero_bna, zero, refl_a, zm]);
    let a_zero = cadd(d, p, a, zero);
    let az = d.lemma(creal.add_zero, &[a]); // Equiv(a_zero, a)

    chain(d, p, lhs, &[(a_zero, congr), (a, az)])
}

/// `Equiv (lerp_raw a b one) b`.
fn lerp_scalar_one_proof(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    let creal = p.creal;
    let one = d.kernel().const_(creal.one, vec![]);
    let na = cneg(d, p, a);
    let b_na = cadd(d, p, b, na);
    let mul_one_bna = cmul(d, p, one, b_na);
    let lhs = cadd(d, p, a, mul_one_bna);

    let om = one_mul_proof(d, p, b_na); // Equiv(mul_one_bna, b_na)
    let refl_a = refl(d, p, a);
    let congr = d.lemma(creal.add_congr, &[a, a, mul_one_bna, b_na, refl_a, om]);
    let a_b_na = cadd(d, p, a, b_na);
    let acm = add_cancel_middle_proof(d, p, a, b); // Equiv(a_b_na, b)

    chain(d, p, lhs, &[(a_b_na, congr), (b, acm)])
}

/// `Equiv (lerp_raw a b inv2) (midpoint a b)`.
fn lerp_scalar_half_proof(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let na = cneg(d, p, a);
    let b_na = cadd(d, p, b, na);
    let mul_inv2_bna = cmul(d, p, inv2, b_na);
    let lhs = cadd(d, p, a, mul_inv2_bna);

    let ib = cmul(d, p, inv2, b);
    let ia = cmul(d, p, inv2, a);
    let neg_ia = cneg(d, p, ia);
    let ib_negia = cadd(d, p, ib, neg_ia);
    let msr = mul_sub_right_proof(d, p, inv2, b, a); // Equiv(mul_inv2_bna, ib_negia)

    let refl_a = refl(d, p, a);
    let congr1 = d.lemma(
        creal.add_congr,
        &[a, a, mul_inv2_bna, ib_negia, refl_a, msr],
    );
    let a_ib_negia = cadd(d, p, a, ib_negia);

    // a ~ ia + ia
    let hd = half_double_proof(d, p, a); // Equiv(a, ia_ia)
    let ia_ia = cadd(d, p, ia, ia);
    let refl_ib_negia = refl(d, p, ib_negia);
    let congr2 = d.lemma(
        creal.add_congr,
        &[a, ia_ia, ib_negia, ib_negia, hd, refl_ib_negia],
    );
    let ia_ia_ib_negia = cadd(d, p, ia_ia, ib_negia);

    // (Z + (ib + neg ia)) ~ (Z + ib) + neg ia,  Z := ia+ia
    let z_ib = cadd(d, p, ia_ia, ib);
    let z_ib_negia = cadd(d, p, z_ib, neg_ia);
    let assoc_z = d.lemma(creal.add_assoc, &[ia_ia, ib, neg_ia]); // Equiv(z_ib_negia, ia_ia_ib_negia)
    let assoc_z_symm = symm(d, p, z_ib_negia, ia_ia_ib_negia, assoc_z);

    // Z + ib ~ (ia+ib) + ia
    let ia_ib = cadd(d, p, ia, ib);
    let ia_iaib = cadd(d, p, ia, ia_ib);
    let assoc1 = d.lemma(creal.add_assoc, &[ia, ia, ib]); // Equiv(z_ib, ia_iaib)
    let comm_ia_ib = d.lemma(creal.add_comm, &[ia, ib]); // Equiv(ia_ib, ib_ia)
    let ib_ia = cadd(d, p, ib, ia);
    let refl_ia = refl(d, p, ia);
    let congr_ia = d.lemma(
        creal.add_congr,
        &[ia, ia, ia_ib, ib_ia, refl_ia, comm_ia_ib],
    );
    let ia_ibia = cadd(d, p, ia, ib_ia);
    let iaib_ia = cadd(d, p, ia_ib, ia);
    let assoc2 = d.lemma(creal.add_assoc, &[ia, ib, ia]); // Equiv(iaib_ia, ia_ibia)
    let assoc2_symm = symm(d, p, iaib_ia, ia_ibia, assoc2);

    let z_ib_to_iaibia = chain(
        d,
        p,
        z_ib,
        &[
            (ia_iaib, assoc1),
            (ia_ibia, congr_ia),
            (iaib_ia, assoc2_symm),
        ],
    );

    let refl_negia = refl(d, p, neg_ia);
    let congr_zib = d.lemma(
        creal.add_congr,
        &[z_ib, iaib_ia, neg_ia, neg_ia, z_ib_to_iaibia, refl_negia],
    );
    let iaib_ia_negia = cadd(d, p, iaib_ia, neg_ia);

    let asc = add_sub_cancel_right(d, p, ia_ib, ia); // Equiv(iaib_ia_negia, ia_ib)

    let final_zib_negia_chain = chain(
        d,
        p,
        z_ib_negia,
        &[(iaib_ia_negia, congr_zib), (ia_ib, asc)],
    );

    let midpoint_ab = midpoint(d, p, a, b);
    let ld = d.lemma(creal.left_distrib, &[inv2, a, b]); // Equiv(midpoint_ab, ia_ib)
    let ld_symm = symm(d, p, midpoint_ab, ia_ib, ld);

    chain(
        d,
        p,
        lhs,
        &[
            (a_ib_negia, congr1),
            (ia_ia_ib_negia, congr2),
            (z_ib_negia, assoc_z_symm),
            (ia_ib, final_zib_negia_chain),
            (midpoint_ab, ld_symm),
        ],
    )
}

/// `Scalar.lerp a b t := CReal.add a (CReal.mul t (CReal.add b (CReal.neg a)))`.
fn declare_lerp_scalar(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let body = lerp_raw(d, p, a, b, t);
    let value = {
        let inner = d.lam_fv(t_fv, carrier, body);
        let inner2 = d.lam_fv(b_fv, carrier, inner);
        d.lam_fv(a_fv, carrier, inner2)
    };
    let ty = {
        let inner = d.arrow(carrier, carrier);
        let inner2 = d.arrow(carrier, inner);
        d.arrow(carrier, inner2)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.lerp_scalar,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 13),
    })
}

/// `CPoint.lerp P Q t := CPoint.mk (Scalar.lerp (x P) (x Q) t) (Scalar.lerp
/// (y P) (y Q) t)`.
fn declare_point_lerp(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let lx = d.const_app(p.lerp_scalar, &[ax, bx, t]);
    let ly = d.const_app(p.lerp_scalar, &[ay, by, t]);
    let value_body = d.const_app(p.mk, &[lx, ly]);

    let value = {
        let inner = d.lam_fv(t_fv, carrier, value_body);
        let inner2 = d.lam_fv(pb_fv, point, inner);
        d.lam_fv(pa_fv, point, inner2)
    };
    let ty = {
        let inner = d.arrow(carrier, point);
        let inner2 = d.arrow(point, inner);
        d.arrow(point, inner2)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.point_lerp,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 14),
    })
}

/// `lerp_zero : ∀ B C, CPoint.Equiv (lerp B C zero) B`.
fn declare_lerp_zero(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);
    let zero = czero(d, p);

    let proof_x = lerp_scalar_zero_proof(d, p, bx, cx);
    let proof_y = lerp_scalar_zero_proof(d, p, by, cy);

    let claim_x = {
        let lerp_x = d.const_app(p.lerp_scalar, &[bx, cx, zero]);
        equiv(d, p, lerp_x, bx)
    };
    let claim_y = {
        let lerp_y = d.const_app(p.lerp_scalar, &[by, cy, zero]);
        equiv(d, p, lerp_y, by)
    };
    let proof = and_intro(d, p, claim_x, claim_y, proof_x, proof_y);

    let big_d = d.const_app(p.point_lerp, &[pb, pc, zero]);
    let ty_body = d.const_app(p.point_equiv, &[big_d, pb]);

    let ty = {
        let inner = d.pi_fv(c_fv, point, ty_body);
        d.pi_fv(b_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(c_fv, point, proof);
        d.lam_fv(b_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lerp_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `lerp_one : ∀ B C, CPoint.Equiv (lerp B C one) C`.
fn declare_lerp_one(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);
    let one = d.kernel().const_(creal.one, vec![]);

    let proof_x = lerp_scalar_one_proof(d, p, bx, cx);
    let proof_y = lerp_scalar_one_proof(d, p, by, cy);

    let claim_x = {
        let lerp_x = d.const_app(p.lerp_scalar, &[bx, cx, one]);
        equiv(d, p, lerp_x, cx)
    };
    let claim_y = {
        let lerp_y = d.const_app(p.lerp_scalar, &[by, cy, one]);
        equiv(d, p, lerp_y, cy)
    };
    let proof = and_intro(d, p, claim_x, claim_y, proof_x, proof_y);

    let big_d = d.const_app(p.point_lerp, &[pb, pc, one]);
    let ty_body = d.const_app(p.point_equiv, &[big_d, pc]);

    let ty = {
        let inner = d.pi_fv(c_fv, point, ty_body);
        d.pi_fv(b_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(c_fv, point, proof);
        d.lam_fv(b_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lerp_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `lerp_half_is_midpoint : ∀ B C, CPoint.Equiv (lerp B C inv2) (point_midpoint B C)`.
fn declare_lerp_half_is_midpoint(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);
    let inv2 = d.kernel().const_(p.inv2, vec![]);

    let proof_x = lerp_scalar_half_proof(d, p, bx, cx);
    let proof_y = lerp_scalar_half_proof(d, p, by, cy);

    let claim_x = {
        let lerp_x = d.const_app(p.lerp_scalar, &[bx, cx, inv2]);
        let mid_x = midpoint(d, p, bx, cx);
        equiv(d, p, lerp_x, mid_x)
    };
    let claim_y = {
        let lerp_y = d.const_app(p.lerp_scalar, &[by, cy, inv2]);
        let mid_y = midpoint(d, p, by, cy);
        equiv(d, p, lerp_y, mid_y)
    };
    let proof = and_intro(d, p, claim_x, claim_y, proof_x, proof_y);

    let big_d = d.const_app(p.point_lerp, &[pb, pc, inv2]);
    let mid_point = d.const_app(p.point_midpoint, &[pb, pc]);
    let ty_body = d.const_app(p.point_equiv, &[big_d, mid_point]);

    let ty = {
        let inner = d.pi_fv(c_fv, point, ty_body);
        d.pi_fv(b_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(c_fv, point, proof);
        d.lam_fv(b_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lerp_half_is_midpoint,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The algebraic engine.** `lerp_dist_sq : ∀ P B C t,
/// Equiv (distSq P (lerp B C t))
///   (add (distSq P B)
///        (add (neg (mul t (dot (sub P B) (sub C B))))
///             (add (neg (mul t (dot (sub P B) (sub C B))))
///                  (mul t (mul t (distSq B C))))))`,
/// i.e. `|PD|² = |PB|² − 2t·(P−B)·(C−B) + t²·|BC|²` where `D := lerp B C t`.
fn declare_lerp_dist_sq(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let creal = p.creal;

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv); // P
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv); // B
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv); // C
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv); // t

    let px = d.const_app(p.x, &[pp]);
    let py = d.const_app(p.y, &[pp]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);

    let big_d = d.const_app(p.point_lerp, &[pb, pc, t]); // D := lerp B C t
    let dx = d.const_app(p.x, &[big_d]);
    let dy = d.const_app(p.y, &[big_d]);

    let pv = psub(d, p, pp, pb); // V := P - B
    let pu = psub(d, p, big_d, pb); // U := D - B
    let pw = psub(d, p, pc, pb); // W := C - B

    let neg_bx = cneg(d, p, bx);
    let neg_by = cneg(d, p, by);
    let vx = cadd(d, p, px, neg_bx);
    let vy = cadd(d, p, py, neg_by);
    let ux = cadd(d, p, dx, neg_bx);
    let uy = cadd(d, p, dy, neg_by);
    let wx = cadd(d, p, cx, neg_bx);
    let wy = cadd(d, p, cy, neg_by);

    // === Stage 1: telescope `P - D ~ (P-B) - (D-B)` through B, then
    // dot_self_sub(V,U) expands `distSq P D`. ===
    let dd_x = diff_diff_scalar_proof(d, p, px, dx, bx); // Equiv(px-dx, vx-ux)
    let dd_y = diff_diff_scalar_proof(d, p, py, dy, by);

    let sub_pd = psub(d, p, pp, big_d);
    let sub_vu = psub(d, p, pv, pu);

    let tele_fact = {
        let neg_dx = cneg(d, p, dx);
        let lhs_x = cadd(d, p, px, neg_dx);
        let neg_ux = cneg(d, p, ux);
        let rhs_x = cadd(d, p, vx, neg_ux);
        let claim_x = equiv(d, p, lhs_x, rhs_x);
        let neg_dy = cneg(d, p, dy);
        let lhs_y = cadd(d, p, py, neg_dy);
        let neg_uy = cneg(d, p, uy);
        let rhs_y = cadd(d, p, vy, neg_uy);
        let claim_y = equiv(d, p, lhs_y, rhs_y);
        and_intro(d, p, claim_x, claim_y, dd_x, dd_y)
    };

    let dot_pd_pd = dotp(d, p, sub_pd, sub_pd);
    let dot_vu_vu = dotp(d, p, sub_vu, sub_vu);
    let pd_congr = d.lemma(
        p.dot_congr,
        &[sub_pd, sub_vu, sub_pd, sub_vu, tele_fact, tele_fact],
    );
    let pd_expand = d.lemma(p.dot_self_sub, &[pv, pu]);

    let dot_vv = dotp(d, p, pv, pv);
    let dot_vu = dotp(d, p, pv, pu);
    let dot_uu = dotp(d, p, pu, pu);
    let neg_dot_vu = cneg(d, p, dot_vu);
    let expand_rhs = {
        let inner = cadd(d, p, neg_dot_vu, dot_uu);
        let mid = cadd(d, p, neg_dot_vu, inner);
        cadd(d, p, dot_vv, mid)
    };

    let pd_total = chain(
        d,
        p,
        dot_pd_pd,
        &[(dot_vu_vu, pd_congr), (expand_rhs, pd_expand)],
    );

    // === Stage 2: `dot(U,U) ~ mul t (mul t (distSq B C))`, using `U ~ t·W`
    // (`D - B ~ t*(C-B)` falls out of `lerp`'s own definition via
    // `add_sub_cancel_left`). ===
    let mul_t_wx = cmul(d, p, t, wx);
    let mul_t_wy = cmul(d, p, t, wy);
    let ux_scale = add_sub_cancel_left(d, p, bx, mul_t_wx); // bridges to Equiv(ux, mul_t_wx)
    let uy_scale = add_sub_cancel_left(d, p, by, mul_t_wy);

    let tw_raw = d.const_app(p.mk, &[mul_t_wx, mul_t_wy]);
    let u_tw_fact = {
        let claim_x = equiv(d, p, ux, mul_t_wx);
        let claim_y = equiv(d, p, uy, mul_t_wy);
        and_intro(d, p, claim_x, claim_y, ux_scale, uy_scale)
    };

    let dot_uu_tw = dotp(d, p, tw_raw, tw_raw);
    let dot_uu_congr = d.lemma(p.dot_congr, &[pu, tw_raw, pu, tw_raw, u_tw_fact, u_tw_fact]);
    // Equiv(dot_uu, dot_uu_tw)

    let sq_wx = cmul(d, p, mul_t_wx, mul_t_wx);
    let sq_wy = cmul(d, p, mul_t_wy, mul_t_wy);
    let dot_uu_tw_raw = cadd(d, p, sq_wx, sq_wy); // =defeq= dot_uu_tw
    let refl_dot_uu_tw = refl(d, p, dot_uu_tw);

    let sqx = sq_scale_proof(d, p, t, wx); // Equiv(sq_wx, t*(t*(wx*wx)))
    let sqy = sq_scale_proof(d, p, t, wy);

    let wxwx = cmul(d, p, wx, wx);
    let wywy = cmul(d, p, wy, wy);
    let t_wxwx = cmul(d, p, t, wxwx);
    let t_wywy = cmul(d, p, t, wywy);
    let tt_wxwx = cmul(d, p, t, t_wxwx);
    let tt_wywy = cmul(d, p, t, t_wywy);

    let sum_scaled = cadd(d, p, tt_wxwx, tt_wywy);
    let combine_sq = d.lemma(creal.add_congr, &[sq_wx, tt_wxwx, sq_wy, tt_wywy, sqx, sqy]); // Equiv(dot_uu_tw_raw, sum_scaled)

    // sum_scaled ~ t*(t_wxwx + t_wywy)   [symm(left_distrib(t, t_wxwx, t_wywy))]
    let t_wxwx_wywy = cadd(d, p, t_wxwx, t_wywy);
    let t_sum1 = cmul(d, p, t, t_wxwx_wywy);
    let ld_outer = d.lemma(creal.left_distrib, &[t, t_wxwx, t_wywy]); // Equiv(t_sum1, sum_scaled)
    let ld_outer_symm = symm(d, p, t_sum1, sum_scaled, ld_outer); // Equiv(sum_scaled, t_sum1)

    // t_wxwx_wywy ~ t*(wxwx+wywy)   [symm(left_distrib(t, wxwx, wywy))]
    let wxwx_wywy = cadd(d, p, wxwx, wywy);
    let t_wxwx_wywy_prod = cmul(d, p, t, wxwx_wywy);
    let ld_inner = d.lemma(creal.left_distrib, &[t, wxwx, wywy]); // Equiv(t_wxwx_wywy_prod, t_wxwx_wywy)
    let ld_inner_symm = symm(d, p, t_wxwx_wywy_prod, t_wxwx_wywy, ld_inner); // Equiv(t_wxwx_wywy, t_wxwx_wywy_prod)

    let refl_t_a = refl(d, p, t);
    let tt_ww_congr = d.lemma(
        creal.mul_congr,
        &[t, t, t_wxwx_wywy, t_wxwx_wywy_prod, refl_t_a, ld_inner_symm],
    ); // Equiv(t_sum1, mul t t_wxwx_wywy_prod)
    let tt_ww = cmul(d, p, t, t_wxwx_wywy_prod);

    // distSq C B =defeq= wxwx_wywy; dist_sq_comm flips it to distSq B C.
    let dsq_cb_named = d.const_app(p.dist_sq, &[pc, pb]);
    let dsq_bc_named = d.const_app(p.dist_sq, &[pb, pc]);
    let bridge_cb = refl(d, p, wxwx_wywy); // Equiv(wxwx_wywy, dsq_cb_named), by defeq
    let comm_bc = d.lemma(p.dist_sq_comm, &[pc, pb]); // Equiv(dsq_cb_named, dsq_bc_named)
    let wxwx_wywy_to_named = chain(
        d,
        p,
        wxwx_wywy,
        &[(dsq_cb_named, bridge_cb), (dsq_bc_named, comm_bc)],
    );

    let refl_t_b = refl(d, p, t);
    let inner_named_congr = d.lemma(
        creal.mul_congr,
        &[t, t, wxwx_wywy, dsq_bc_named, refl_t_b, wxwx_wywy_to_named],
    ); // Equiv(t_wxwx_wywy_prod, mul t dsq_bc_named)
    let t_dsq_bc = cmul(d, p, t, dsq_bc_named);

    let refl_t_c = refl(d, p, t);
    let outer_named_congr = d.lemma(
        creal.mul_congr,
        &[
            t,
            t,
            t_wxwx_wywy_prod,
            t_dsq_bc,
            refl_t_c,
            inner_named_congr,
        ],
    ); // Equiv(tt_ww, mul t t_dsq_bc)
    let tt_dsq_bc = cmul(d, p, t, t_dsq_bc); // mul t (mul t (distSq B C))

    let uu_final = chain(
        d,
        p,
        dot_uu,
        &[
            (dot_uu_tw, dot_uu_congr),
            (dot_uu_tw_raw, refl_dot_uu_tw),
            (sum_scaled, combine_sq),
            (t_sum1, ld_outer_symm),
            (tt_ww, tt_ww_congr),
            (tt_dsq_bc, outer_named_congr),
        ],
    ); // Equiv(dot_uu, mul t (mul t (distSq B C)))

    // === Stage 3: `dot(V,U) ~ mul t (dot V W)`. ===
    let refl_pv = point_equiv_refl(d, p, pv);
    let dot_v_tw = dotp(d, p, pv, tw_raw);
    let dot_vu_congr2 = d.lemma(p.dot_congr, &[pv, pv, pu, tw_raw, refl_pv, u_tw_fact]);
    // Equiv(dot_vu, dot_v_tw)

    let vxtwx = cmul(d, p, vx, mul_t_wx);
    let vytwy = cmul(d, p, vy, mul_t_wy);
    let dot_v_tw_raw = cadd(d, p, vxtwx, vytwy); // =defeq= dot_v_tw
    let refl_dot_v_tw = refl(d, p, dot_v_tw);

    let swap_x = mul_left_swap_proof(d, p, t, vx, wx); // Equiv(vxtwx, t*(vx*wx))
    let swap_y = mul_left_swap_proof(d, p, t, vy, wy);
    let vxwx = cmul(d, p, vx, wx);
    let vywy = cmul(d, p, vy, wy);
    let t_vxwx = cmul(d, p, t, vxwx);
    let t_vywy = cmul(d, p, t, vywy);
    let sum_v_scaled = cadd(d, p, t_vxwx, t_vywy);
    let combine_v = d.lemma(
        creal.add_congr,
        &[vxtwx, t_vxwx, vytwy, t_vywy, swap_x, swap_y],
    ); // Equiv(dot_v_tw_raw, sum_v_scaled)

    let vxwx_vywy = cadd(d, p, vxwx, vywy);
    let t_vxwx_vywy = cmul(d, p, t, vxwx_vywy);
    let ld_v = d.lemma(creal.left_distrib, &[t, vxwx, vywy]); // Equiv(t_vxwx_vywy, sum_v_scaled)
    let ld_v_symm = symm(d, p, t_vxwx_vywy, sum_v_scaled, ld_v); // Equiv(sum_v_scaled, t_vxwx_vywy)

    let dot_vw = dotp(d, p, pv, pw); // =defeq= vxwx_vywy
    let bridge_vw = refl(d, p, vxwx_vywy); // Equiv(vxwx_vywy, dot_vw)
    let refl_t_d = refl(d, p, t);
    let t_dot_vw_congr = d.lemma(
        creal.mul_congr,
        &[t, t, vxwx_vywy, dot_vw, refl_t_d, bridge_vw],
    ); // Equiv(t_vxwx_vywy, mul t dot_vw)
    let t_dot_vw = cmul(d, p, t, dot_vw);

    let vu_final = chain(
        d,
        p,
        dot_vu,
        &[
            (dot_v_tw, dot_vu_congr2),
            (dot_v_tw_raw, refl_dot_v_tw),
            (sum_v_scaled, combine_v),
            (t_vxwx_vywy, ld_v_symm),
            (t_dot_vw, t_dot_vw_congr),
        ],
    ); // Equiv(dot_vu, mul t (dot (sub P B) (sub C B)))

    // === Stage 4: substitute uu_final/vu_final into expand_rhs. ===
    let neg_t_dot_vw = cneg(d, p, t_dot_vw);
    let neg_congr = d.lemma(creal.neg_congr, &[dot_vu, t_dot_vw, vu_final]);
    // Equiv(neg_dot_vu, neg_t_dot_vw)

    let inner_step = d.lemma(
        creal.add_congr,
        &[
            neg_dot_vu,
            neg_t_dot_vw,
            dot_uu,
            tt_dsq_bc,
            neg_congr,
            uu_final,
        ],
    ); // Equiv(inner, target_inner)
    let target_inner = cadd(d, p, neg_t_dot_vw, tt_dsq_bc);

    let inner_raw = cadd(d, p, neg_dot_vu, dot_uu);
    let mid_before = cadd(d, p, neg_dot_vu, inner_raw);
    let mid_step = d.lemma(
        creal.add_congr,
        &[
            neg_dot_vu,
            neg_t_dot_vw,
            inner_raw,
            target_inner,
            neg_congr,
            inner_step,
        ],
    );
    let target_mid = cadd(d, p, neg_t_dot_vw, target_inner);

    let dsq_pb_named = d.const_app(p.dist_sq, &[pp, pb]);
    let bridge_pb = refl(d, p, dot_vv); // Equiv(dot_vv, dsq_pb_named), by defeq
    let outer_step = d.lemma(
        creal.add_congr,
        &[
            dot_vv,
            dsq_pb_named,
            mid_before,
            target_mid,
            bridge_pb,
            mid_step,
        ],
    );
    let target_full = cadd(d, p, dsq_pb_named, target_mid);

    let final_proof = chain(
        d,
        p,
        dot_pd_pd,
        &[(expand_rhs, pd_total), (target_full, outer_step)],
    );

    // === State the theorem over the named `distSq`/`lerp`/`dot`/`sub` forms. ===
    let dsq_p_lerp = d.const_app(p.dist_sq, &[pp, big_d]);
    let ty_body = equiv(d, p, dsq_p_lerp, target_full);

    let ty = {
        let w3 = d.pi_fv(t_fv, carrier, ty_body);
        let w2 = d.pi_fv(c_fv, point, w3);
        let w1 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(pp_fv, point, w1)
    };
    let value = {
        let w3 = d.lam_fv(t_fv, carrier, final_proof);
        let w2 = d.lam_fv(c_fv, point, w3);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(pp_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lerp_dist_sq,
        uparams: vec![],
        ty,
        value,
    })
}

// --- Stewart's theorem, squared/parametric form -----------------------------

/// `Equiv (mul t (mul (add one (neg t)) z)) (add (mul t z) (neg (mul t (mul t z))))`
/// — `t·((1−t)·z) ~ t·z − t·(t·z)`.
fn s1_proof(d: &mut IntDev<'_>, p: CPointPrelude, t: ExprId, z: ExprId) -> ExprId {
    let creal = p.creal;
    let one = d.kernel().const_(creal.one, vec![]);
    let neg_t = cneg(d, p, t);
    let one_neg_t = cadd(d, p, one, neg_t);
    let mul_one_neg_t_z = cmul(d, p, one_neg_t, z);
    let lhs = cmul(d, p, t, mul_one_neg_t_z);

    let mul_one_z = cmul(d, p, one, z);
    let mul_negt_z = cmul(d, p, neg_t, z);
    let ab = cadd(d, p, mul_one_z, mul_negt_z);
    let rd = right_distrib_proof(d, p, one, neg_t, z); // Equiv(mul_one_neg_t_z, ab)

    let mo = one_mul_proof(d, p, z); // Equiv(mul_one_z, z)
    let mul_t_z = cmul(d, p, t, z);
    let neg_mul_t_z = cneg(d, p, mul_t_z);
    let mnl = mul_neg_left_proof(d, p, t, z); // Equiv(mul_negt_z, neg_mul_t_z)
    let congr1 = d.lemma(
        creal.add_congr,
        &[mul_one_z, z, mul_negt_z, neg_mul_t_z, mo, mnl],
    );
    let z_neg_mtz = cadd(d, p, z, neg_mul_t_z);

    let step1 = chain(d, p, mul_one_neg_t_z, &[(ab, rd), (z_neg_mtz, congr1)]);

    let refl_t = refl(d, p, t);
    let t_z_neg_mtz = cmul(d, p, t, z_neg_mtz);
    let congr2 = d.lemma(
        creal.mul_congr,
        &[t, t, mul_one_neg_t_z, z_neg_mtz, refl_t, step1],
    );

    let mul_t_negmtz = cmul(d, p, t, neg_mul_t_z);
    let ld_rhs = cadd(d, p, mul_t_z, mul_t_negmtz);
    let ld = d.lemma(creal.left_distrib, &[t, z, neg_mul_t_z]); // Equiv(t_z_neg_mtz, ld_rhs)

    let mul_t_mtz = cmul(d, p, t, mul_t_z);
    let neg_mul_t_mtz = cneg(d, p, mul_t_mtz);
    let mnr = mul_neg_right_proof(d, p, t, mul_t_z); // Equiv(mul_t_negmtz, neg_mul_t_mtz)
    let refl_mtz = refl(d, p, mul_t_z);
    let congr3 = d.lemma(
        creal.add_congr,
        &[mul_t_z, mul_t_z, mul_t_negmtz, neg_mul_t_mtz, refl_mtz, mnr],
    );
    let target = cadd(d, p, mul_t_z, neg_mul_t_mtz);

    chain(
        d,
        p,
        lhs,
        &[(t_z_neg_mtz, congr2), (ld_rhs, ld), (target, congr3)],
    )
}

/// `Equiv (mul (add one (neg t)) x) (add x (neg (mul t x)))` — `(1−t)·x ~ x − t·x`.
fn s2_proof(d: &mut IntDev<'_>, p: CPointPrelude, t: ExprId, x: ExprId) -> ExprId {
    let creal = p.creal;
    let one = d.kernel().const_(creal.one, vec![]);
    let neg_t = cneg(d, p, t);
    let one_neg_t = cadd(d, p, one, neg_t);
    let lhs = cmul(d, p, one_neg_t, x);

    let mul_one_x = cmul(d, p, one, x);
    let mul_negt_x = cmul(d, p, neg_t, x);
    let ab = cadd(d, p, mul_one_x, mul_negt_x);
    let rd = right_distrib_proof(d, p, one, neg_t, x); // Equiv(lhs, ab)

    let mo = one_mul_proof(d, p, x); // Equiv(mul_one_x, x)
    let mul_t_x = cmul(d, p, t, x);
    let neg_mul_t_x = cneg(d, p, mul_t_x);
    let mnl = mul_neg_left_proof(d, p, t, x); // Equiv(mul_negt_x, neg_mul_t_x)
    let congr = d.lemma(
        creal.add_congr,
        &[mul_one_x, x, mul_negt_x, neg_mul_t_x, mo, mnl],
    );
    let target = cadd(d, p, x, neg_mul_t_x);

    chain(d, p, lhs, &[(ab, rd), (target, congr)])
}

/// `Equiv (mul t (add x (add (neg y) (add (neg y) z))))
///        (add (mul t x) (add (neg (mul t y)) (add (neg (mul t y)) (mul t z))))`
/// — `t·(x − 2y + z) ~ t·x − 2·(t·y) + t·z`.
fn s3_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    t: ExprId,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> ExprId {
    let creal = p.creal;
    let neg_y = cneg(d, p, y);
    let neg_y_z = cadd(d, p, neg_y, z);
    let inner = cadd(d, p, neg_y, neg_y_z);
    let x_inner = cadd(d, p, x, inner);
    let lhs = cmul(d, p, t, x_inner);

    let mul_t_x = cmul(d, p, t, x);
    let mul_t_inner = cmul(d, p, t, inner);
    let mtx_mtinner = cadd(d, p, mul_t_x, mul_t_inner);
    let ld1 = d.lemma(creal.left_distrib, &[t, x, inner]); // Equiv(lhs, mtx_mtinner)

    let mul_t_negy = cmul(d, p, t, neg_y);
    let mul_t_negyz = cmul(d, p, t, neg_y_z);
    let step_ab = cadd(d, p, mul_t_negy, mul_t_negyz);
    let ld2 = d.lemma(creal.left_distrib, &[t, neg_y, neg_y_z]); // Equiv(mul_t_inner, step_ab)

    let mul_t_y = cmul(d, p, t, y);
    let neg_mul_t_y = cneg(d, p, mul_t_y);
    let mnr1 = mul_neg_right_proof(d, p, t, y); // Equiv(mul_t_negy, neg_mul_t_y)

    let mul_t_z = cmul(d, p, t, z);
    let mtnegy_mtz = cadd(d, p, mul_t_negy, mul_t_z);
    let ld3 = d.lemma(creal.left_distrib, &[t, neg_y, z]); // Equiv(mul_t_negyz, mtnegy_mtz)

    let refl_mtz = refl(d, p, mul_t_z);
    let congr_a = d.lemma(
        creal.add_congr,
        &[mul_t_negy, neg_mul_t_y, mul_t_z, mul_t_z, mnr1, refl_mtz],
    );
    let neg_mty_mtz = cadd(d, p, neg_mul_t_y, mul_t_z);
    let negyz_reduce = chain(
        d,
        p,
        mul_t_negyz,
        &[(mtnegy_mtz, ld3), (neg_mty_mtz, congr_a)],
    );

    let refl_mtnegy = refl(d, p, mul_t_negy);
    let congr_b = d.lemma(
        creal.add_congr,
        &[
            mul_t_negy,
            neg_mul_t_y,
            mul_t_negyz,
            neg_mty_mtz,
            mnr1,
            negyz_reduce,
        ],
    );
    let _ = refl_mtnegy;
    let target_inner = cadd(d, p, neg_mul_t_y, neg_mty_mtz);
    let inner_total = chain(
        d,
        p,
        mul_t_inner,
        &[(step_ab, ld2), (target_inner, congr_b)],
    );

    let refl_mtx = refl(d, p, mul_t_x);
    let congr_outer = d.lemma(
        creal.add_congr,
        &[
            mul_t_x,
            mul_t_x,
            mul_t_inner,
            target_inner,
            refl_mtx,
            inner_total,
        ],
    );
    let target = cadd(d, p, mul_t_x, target_inner);

    chain(d, p, lhs, &[(mtx_mtinner, ld1), (target, congr_outer)])
}

/// Given opaque `CReal` terms `x, pp, qq, rr, ss` (`pp := t·X`, `qq := t·Y`,
/// `rr := t·(t·Z)`, `ss := t·Z`), proves
/// `Equiv (add (add x (add (neg qq) (add (neg qq) rr))) (add ss (neg rr)))
///        (add (add x (neg pp)) (add pp (add (neg qq) (add (neg qq) ss))))`,
/// i.e. `(x − 2qq + rr) + (ss − rr) ~ (x − pp) + (pp − 2qq + ss)` — both sides
/// reduce to `x − 2qq + ss`. Pure `CReal` ring algebra, the final combination
/// step [`CPointPrelude::stewart`] needs after [`s1_proof`]/[`s2_proof`]/
/// [`s3_proof`] have turned every `(1−t)`-weighted term into a difference.
fn stewart_ring_core_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    pp: ExprId,
    qq: ExprId,
    rr: ExprId,
    ss: ExprId,
) -> ExprId {
    let creal = p.creal;
    let neg_qq = cneg(d, p, qq);
    let neg_rr = cneg(d, p, rr);
    let neg_pp = cneg(d, p, pp);

    let qq_rr = cadd(d, p, neg_qq, rr);
    let b = cadd(d, p, neg_qq, qq_rr);
    let a1 = cadd(d, p, x, b);
    let c = cadd(d, p, ss, neg_rr);
    let lhs = cadd(d, p, a1, c); // LHS''

    let assoc1 = d.lemma(creal.add_assoc, &[x, b, c]); // Equiv(lhs, x+(b+c))
    let bc = cadd(d, p, b, c);
    let x_bc = cadd(d, p, x, bc);

    let assoc2 = d.lemma(creal.add_assoc, &[neg_qq, qq_rr, c]); // Equiv(bc, neg_qq+(qq_rr+c))
    let qqrr_c = cadd(d, p, qq_rr, c);
    let negqq_qqrrc = cadd(d, p, neg_qq, qqrr_c);

    let swap = add_middle_swap_proof(d, p, neg_qq, rr, ss, neg_rr);
    // Equiv((neg_qq+rr)+(ss+neg_rr), (neg_qq+ss)+(rr+neg_rr))
    let negqq_ss = cadd(d, p, neg_qq, ss);
    let rr_negrr = cadd(d, p, rr, neg_rr);
    let negqqss_rrnegrr = cadd(d, p, negqq_ss, rr_negrr);

    let an_rr = d.lemma(creal.add_neg, &[rr]); // Equiv(rr_negrr, zero)
    let zero = czero(d, p);
    let refl_negqqss = refl(d, p, negqq_ss);
    let congr_zero = d.lemma(
        creal.add_congr,
        &[negqq_ss, negqq_ss, rr_negrr, zero, refl_negqqss, an_rr],
    );
    let negqqss_zero = cadd(d, p, negqq_ss, zero);
    let az = d.lemma(creal.add_zero, &[negqq_ss]); // Equiv(negqqss_zero, negqq_ss)

    let qqrrc_reduce = chain(
        d,
        p,
        qqrr_c,
        &[
            (negqqss_rrnegrr, swap),
            (negqqss_zero, congr_zero),
            (negqq_ss, az),
        ],
    ); // Equiv(qqrr_c, negqq_ss)

    let refl_negqq = refl(d, p, neg_qq);
    let congr_b = d.lemma(
        creal.add_congr,
        &[neg_qq, neg_qq, qqrr_c, negqq_ss, refl_negqq, qqrrc_reduce],
    );
    let negqq_negqqss = cadd(d, p, neg_qq, negqq_ss);

    let bc_reduce = chain(d, p, bc, &[(negqq_qqrrc, assoc2), (negqq_negqqss, congr_b)]);
    // Equiv(bc, negqq_negqqss)

    let target = cadd(d, p, x, negqq_negqqss); // TARGET = x + (neg_qq + (neg_qq + ss))
    let refl_x = refl(d, p, x);
    let congr_final = d.lemma(
        creal.add_congr,
        &[x, x, bc, negqq_negqqss, refl_x, bc_reduce],
    );

    let lhs_to_target = chain(d, p, lhs, &[(x_bc, assoc1), (target, congr_final)]);
    // Equiv(LHS'', TARGET)

    // --- RHS'' ~ TARGET ---
    let d_ = negqq_negqqss; // D := neg_qq + (neg_qq + ss)
    let x_negpp = cadd(d, p, x, neg_pp);
    let pp_d = cadd(d, p, pp, d_);
    let rhs = cadd(d, p, x_negpp, pp_d); // RHS''

    let assoc3 = d.lemma(creal.add_assoc, &[x, neg_pp, pp_d]); // Equiv(rhs, x+(neg_pp+pp_d))
    let negpp_ppd = cadd(d, p, neg_pp, pp_d);
    let x_negppppd = cadd(d, p, x, negpp_ppd);

    let assoc4 = d.lemma(creal.add_assoc, &[neg_pp, pp, d_]); // Equiv((neg_pp+pp)+D, negpp_ppd)
    let negpp_pp = cadd(d, p, neg_pp, pp);
    let negpp_pp_d = cadd(d, p, negpp_pp, d_);
    let assoc4_symm = symm(d, p, negpp_pp_d, negpp_ppd, assoc4); // Equiv(negpp_ppd, negpp_pp_d)

    let cancel_pp = neg_add_cancel_proof(d, p, pp); // Equiv(negpp_pp, zero)
    let zero2 = czero(d, p);
    let refl_d = refl(d, p, d_);
    let congr_cancel = d.lemma(
        creal.add_congr,
        &[negpp_pp, zero2, d_, d_, cancel_pp, refl_d],
    );
    let zero_d = cadd(d, p, zero2, d_);
    let zad = zero_add_proof(d, p, d_); // Equiv(zero_d, D)

    let negpp_ppd_reduce = chain(
        d,
        p,
        negpp_ppd,
        &[(negpp_pp_d, assoc4_symm), (zero_d, congr_cancel), (d_, zad)],
    ); // Equiv(negpp_ppd, D)

    let refl_x2 = refl(d, p, x);
    let congr_final2 = d.lemma(
        creal.add_congr,
        &[x, x, negpp_ppd, d_, refl_x2, negpp_ppd_reduce],
    );

    let rhs_to_target = chain(d, p, rhs, &[(x_negppppd, assoc3), (target, congr_final2)]);
    // Equiv(RHS'', TARGET)
    let target_to_rhs = symm(d, p, rhs, target, rhs_to_target); // Equiv(TARGET, RHS'')

    chain(d, p, lhs, &[(target, lhs_to_target), (rhs, target_to_rhs)])
}

/// **Stewart's theorem, squared/parametric form.** `stewart : ∀ A B C t,
/// Equiv (add (distSq A (lerp B C t)) (mul t (mul (add one (neg t)) (distSq B C))))
///       (add (mul (add one (neg t)) (distSq A B)) (mul t (distSq A C)))`.
fn declare_stewart(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);

    // === fact1: distSq A (lerp B C t) ~ X + (-tY + (-tY + t^2 Z)) ===
    let fact1 = d.lemma(p.lerp_dist_sq, &[pa, pb, pc, t]);

    let pv = psub(d, p, pa, pb); // A - B
    let pw = psub(d, p, pc, pb); // C - B
    let dot_vw = dotp(d, p, pv, pw); // Y := dot(A-B, C-B)
    let x_ = d.const_app(p.dist_sq, &[pa, pb]); // X := distSq A B
    let z_ = d.const_app(p.dist_sq, &[pb, pc]); // Z := distSq B C
    let t_y = cmul(d, p, t, dot_vw);
    let neg_ty = cneg(d, p, t_y);
    let t_z = cmul(d, p, t, z_);
    let tt_z = cmul(d, p, t, t_z);

    let fact1_inner = cadd(d, p, neg_ty, tt_z);
    let fact1_mid = cadd(d, p, neg_ty, fact1_inner);
    let fact1_rhs = cadd(d, p, x_, fact1_mid);

    // === fact2: distSq A C ~ X + (-Y + (-Y + Z)), via dot_self_sub through B ===
    let neg_bx = cneg(d, p, bx);
    let neg_by = cneg(d, p, by);
    let vx = cadd(d, p, ax, neg_bx);
    let vy = cadd(d, p, ay, neg_by);
    let wx = cadd(d, p, cx, neg_bx);
    let wy = cadd(d, p, cy, neg_by);

    let dd2_x = diff_diff_scalar_proof(d, p, ax, cx, bx); // Equiv(ax-cx, vx-wx)
    let dd2_y = diff_diff_scalar_proof(d, p, ay, cy, by);

    let sub_ac = psub(d, p, pa, pc);
    let sub_vw = psub(d, p, pv, pw);

    let tele2_fact = {
        let neg_cx = cneg(d, p, cx);
        let lhs_x = cadd(d, p, ax, neg_cx);
        let neg_wx = cneg(d, p, wx);
        let rhs_x = cadd(d, p, vx, neg_wx);
        let claim_x = equiv(d, p, lhs_x, rhs_x);
        let neg_cy = cneg(d, p, cy);
        let lhs_y = cadd(d, p, ay, neg_cy);
        let neg_wy = cneg(d, p, wy);
        let rhs_y = cadd(d, p, vy, neg_wy);
        let claim_y = equiv(d, p, lhs_y, rhs_y);
        and_intro(d, p, claim_x, claim_y, dd2_x, dd2_y)
    };

    let dot_ac_ac = dotp(d, p, sub_ac, sub_ac);
    let dot_vw_vw = dotp(d, p, sub_vw, sub_vw);
    let ac_congr = d.lemma(
        p.dot_congr,
        &[sub_ac, sub_vw, sub_ac, sub_vw, tele2_fact, tele2_fact],
    );
    let ac_expand = d.lemma(p.dot_self_sub, &[pv, pw]);

    let dot_vv2 = dotp(d, p, pv, pv);
    let dot_ww2 = dotp(d, p, pw, pw);
    let neg_dot_vw = cneg(d, p, dot_vw);
    let inner_before2 = cadd(d, p, neg_dot_vw, dot_ww2);
    let mid_before2 = cadd(d, p, neg_dot_vw, inner_before2);
    let ac_rhs_raw = cadd(d, p, dot_vv2, mid_before2);

    let ac_total = chain(
        d,
        p,
        dot_ac_ac,
        &[(dot_vw_vw, ac_congr), (ac_rhs_raw, ac_expand)],
    );

    let dsq_cb2 = d.const_app(p.dist_sq, &[pc, pb]);
    let bridge_ww = refl(d, p, dot_ww2);
    let comm_bc2 = d.lemma(p.dist_sq_comm, &[pc, pb]); // Equiv(dsq_cb2, z_)
    let ww_to_z = chain(d, p, dot_ww2, &[(dsq_cb2, bridge_ww), (z_, comm_bc2)]);

    let refl_negvw = refl(d, p, neg_dot_vw);
    let inner_step2 = d.lemma(
        creal.add_congr,
        &[neg_dot_vw, neg_dot_vw, dot_ww2, z_, refl_negvw, ww_to_z],
    );
    let inner_target2 = cadd(d, p, neg_dot_vw, z_);

    let refl_negvw2 = refl(d, p, neg_dot_vw);
    let mid_step2 = d.lemma(
        creal.add_congr,
        &[
            neg_dot_vw,
            neg_dot_vw,
            inner_before2,
            inner_target2,
            refl_negvw2,
            inner_step2,
        ],
    );
    let mid_target2 = cadd(d, p, neg_dot_vw, inner_target2);

    let bridge_vv2 = refl(d, p, dot_vv2);
    let outer_step2 = d.lemma(
        creal.add_congr,
        &[dot_vv2, x_, mid_before2, mid_target2, bridge_vv2, mid_step2],
    );
    let fact2_target = cadd(d, p, x_, mid_target2);

    let fact2 = chain(
        d,
        p,
        dot_ac_ac,
        &[(ac_rhs_raw, ac_total), (fact2_target, outer_step2)],
    ); // Equiv(dot_ac_ac, fact2_target); dot_ac_ac =defeq= distSq A C

    // === S1: mul t (mul (1-t) Z) ~ add t_z (neg tt_z) ===
    let s1 = s1_proof(d, p, t, z_);

    let one = d.kernel().const_(creal.one, vec![]);
    let neg_t = cneg(d, p, t);
    let one_neg_t = cadd(d, p, one, neg_t);
    let t_one_neg_t_z = cmul(d, p, one_neg_t, z_);
    let mul_t_1mt_z = cmul(d, p, t, t_one_neg_t_z);

    let big_d = d.const_app(p.point_lerp, &[pb, pc, t]);
    let dsq_a_lerp = d.const_app(p.dist_sq, &[pa, big_d]);
    let goal_lhs = cadd(d, p, dsq_a_lerp, mul_t_1mt_z);

    let neg_tt_z = cneg(d, p, tt_z);
    let t_z_negttz = cadd(d, p, t_z, neg_tt_z);
    let goal_lhs_target = cadd(d, p, fact1_rhs, t_z_negttz); // LHS''

    let combine_lhs = d.lemma(
        creal.add_congr,
        &[dsq_a_lerp, fact1_rhs, mul_t_1mt_z, t_z_negttz, fact1, s1],
    ); // Equiv(goal_lhs, goal_lhs_target)

    // === S2/S3: build goal_rhs ~ RHS'' ===
    let s2 = s2_proof(d, p, t, x_);
    let t_x = cmul(d, p, t, x_);
    let neg_t_x = cneg(d, p, t_x);
    let s2_rhs = cadd(d, p, x_, neg_t_x);
    let mul_1mt_x = cmul(d, p, one_neg_t, x_);

    let dsq_ac_named = d.const_app(p.dist_sq, &[pa, pc]);
    let mul_t_dsqac = cmul(d, p, t, dsq_ac_named);
    let goal_rhs = cadd(d, p, mul_1mt_x, mul_t_dsqac);

    let refl_t_e = refl(d, p, t);
    let dsqac_to_fact2 = d.lemma(
        creal.mul_congr,
        &[t, t, dsq_ac_named, fact2_target, refl_t_e, fact2],
    );
    let mul_t_fact2target = cmul(d, p, t, fact2_target);

    let s3 = s3_proof(d, p, t, x_, dot_vw, z_);
    let s3_inner = cadd(d, p, neg_ty, t_z);
    let s3_mid = cadd(d, p, neg_ty, s3_inner);
    let s3_rhs = cadd(d, p, t_x, s3_mid);

    let mul_t_dsqac_total = chain(
        d,
        p,
        mul_t_dsqac,
        &[(mul_t_fact2target, dsqac_to_fact2), (s3_rhs, s3)],
    ); // Equiv(mul_t_dsqac, s3_rhs)

    let combine_rhs = d.lemma(
        creal.add_congr,
        &[
            mul_1mt_x,
            s2_rhs,
            mul_t_dsqac,
            s3_rhs,
            s2,
            mul_t_dsqac_total,
        ],
    ); // Equiv(goal_rhs, goal_rhs_target)
    let goal_rhs_target = cadd(d, p, s2_rhs, s3_rhs); // RHS''

    // === ring core + assembly ===
    let ring_core = stewart_ring_core_proof(d, p, x_, t_x, t_y, tt_z, t_z);
    // Equiv(goal_lhs_target, goal_rhs_target)

    let goal_rhs_symm = symm(d, p, goal_rhs, goal_rhs_target, combine_rhs);
    // Equiv(goal_rhs_target, goal_rhs)

    let final_proof = chain(
        d,
        p,
        goal_lhs,
        &[
            (goal_lhs_target, combine_lhs),
            (goal_rhs_target, ring_core),
            (goal_rhs, goal_rhs_symm),
        ],
    );

    let ty_body = equiv(d, p, goal_lhs, goal_rhs);
    let carrier = creal_ty(d, p);
    let ty = {
        let w3 = d.pi_fv(t_fv, carrier, ty_body);
        let w2 = d.pi_fv(c_fv, point, w3);
        let w1 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(a_fv, point, w1)
    };
    let value = {
        let w3 = d.lam_fv(t_fv, carrier, final_proof);
        let w2 = d.lam_fv(c_fv, point, w3);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.stewart,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The median corollary of Stewart.** See [`CPointPrelude::stewart_median`].
///
/// [`CPointPrelude::stewart`] instantiated at `t := inv2`, then rewritten:
/// `distSq A (lerp B C inv2) ~ distSq A M` via [`CPointPrelude::dist_sq_congr`]
/// and [`CPointPrelude::lerp_half_is_midpoint`], and both `mul (add one (neg
/// inv2)) …` factors rewritten to `mul inv2 …` via
/// [`CPointPrelude::one_sub_inv2`].
fn declare_stewart_median(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let one = d.kernel().const_(creal.one, vec![]);

    // stewart A B C inv2 : Equiv(lhs_orig, rhs_orig).
    let stewart_inst = d.lemma(p.stewart, &[pa, pb, pc, inv2]);

    let lerp_bc_inv2 = d.const_app(p.point_lerp, &[pb, pc, inv2]);
    let dsq_a_lerp = d.const_app(p.dist_sq, &[pa, lerp_bc_inv2]);
    let neg_inv2 = cneg(d, p, inv2);
    let one_neg_inv2 = cadd(d, p, one, neg_inv2);
    let dsq_bc = d.const_app(p.dist_sq, &[pb, pc]);
    let mul_one_neg_inv2_bc = cmul(d, p, one_neg_inv2, dsq_bc);
    let mul_inv2_that = cmul(d, p, inv2, mul_one_neg_inv2_bc);
    let lhs_orig = cadd(d, p, dsq_a_lerp, mul_inv2_that);

    let dsq_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let mul_one_neg_inv2_ab = cmul(d, p, one_neg_inv2, dsq_ab);
    let dsq_ac = d.const_app(p.dist_sq, &[pa, pc]);
    let mul_inv2_ac = cmul(d, p, inv2, dsq_ac);
    let rhs_orig = cadd(d, p, mul_one_neg_inv2_ab, mul_inv2_ac);

    // distSq A (lerp B C inv2) ~ distSq A M.
    let lerp_half = d.lemma(p.lerp_half_is_midpoint, &[pb, pc]); // Equiv(lerp_bc_inv2, M)
    let big_m = d.const_app(p.point_midpoint, &[pb, pc]);
    let refl_pa = point_equiv_refl(d, p, pa);
    let dsq_congr_am = d.lemma(
        p.dist_sq_congr,
        &[pa, pa, lerp_bc_inv2, big_m, refl_pa, lerp_half],
    ); // Equiv(dsq_a_lerp, dsq_a_m)
    let dsq_a_m = d.const_app(p.dist_sq, &[pa, big_m]);

    let one_sub_inv2 = d.kernel().const_(p.one_sub_inv2, vec![]); // Equiv(one_neg_inv2, inv2)

    // Rewrite the BC factor: mul_one_neg_inv2_bc ~ mul inv2 dsq_bc.
    let refl_dsq_bc = refl(d, p, dsq_bc);
    let congr_bc = d.lemma(
        creal.mul_congr,
        &[
            one_neg_inv2,
            inv2,
            dsq_bc,
            dsq_bc,
            one_sub_inv2,
            refl_dsq_bc,
        ],
    );
    let mul_inv2_bc = cmul(d, p, inv2, dsq_bc);
    let refl_inv2 = refl(d, p, inv2);
    let congr_inner = d.lemma(
        creal.mul_congr,
        &[
            inv2,
            inv2,
            mul_one_neg_inv2_bc,
            mul_inv2_bc,
            refl_inv2,
            congr_bc,
        ],
    );
    let mul_inv2_mul_inv2_bc = cmul(d, p, inv2, mul_inv2_bc);

    let lhs_congr = d.lemma(
        creal.add_congr,
        &[
            dsq_a_lerp,
            dsq_a_m,
            mul_inv2_that,
            mul_inv2_mul_inv2_bc,
            dsq_congr_am,
            congr_inner,
        ],
    ); // Equiv(lhs_orig, lhs_new)
    let lhs_new = cadd(d, p, dsq_a_m, mul_inv2_mul_inv2_bc);

    // Rewrite the AB factor: mul_one_neg_inv2_ab ~ mul inv2 dsq_ab.
    let refl_dsq_ab = refl(d, p, dsq_ab);
    let congr_ab = d.lemma(
        creal.mul_congr,
        &[
            one_neg_inv2,
            inv2,
            dsq_ab,
            dsq_ab,
            one_sub_inv2,
            refl_dsq_ab,
        ],
    );
    let mul_inv2_ab = cmul(d, p, inv2, dsq_ab);
    let refl_mul_inv2_ac = refl(d, p, mul_inv2_ac);
    let rhs_congr = d.lemma(
        creal.add_congr,
        &[
            mul_one_neg_inv2_ab,
            mul_inv2_ab,
            mul_inv2_ac,
            mul_inv2_ac,
            congr_ab,
            refl_mul_inv2_ac,
        ],
    ); // Equiv(rhs_orig, rhs_new)
    let rhs_new = cadd(d, p, mul_inv2_ab, mul_inv2_ac);

    let lhs_congr_symm = symm(d, p, lhs_orig, lhs_new, lhs_congr); // Equiv(lhs_new, lhs_orig)
    let final_proof = chain(
        d,
        p,
        lhs_new,
        &[
            (lhs_orig, lhs_congr_symm),
            (rhs_orig, stewart_inst),
            (rhs_new, rhs_congr),
        ],
    );

    let ty_body = equiv(d, p, lhs_new, rhs_new);
    let ty = {
        let w2 = d.pi_fv(c_fv, point, ty_body);
        let w1 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(a_fv, point, w1)
    };
    let value = {
        let w2 = d.lam_fv(c_fv, point, final_proof);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.stewart_median,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod creal_point_tests;
