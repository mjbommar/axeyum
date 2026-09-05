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
    /// was because the kernel had no `CReal.sqrt`, only `natSqrt`, until
    /// `CReal.sqrt` landed 2026-08-26; the unsigned lengths `BD, DC, BC` are
    /// expressible now (`CReal.sqrt` of the corresponding `distSq`), but the
    /// literal length-product statement `BD·DC·BC + AD²·BC ~ AB²·DC + AC²·BD`
    /// is still not proved here. Multiplying this identity through by the (unsquared) `BC`
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
    /// **The heart of the Euler line: a circumcentre's construction of an
    /// orthocentre.** `∀ O A B C,
    /// Equiv (distSq O A) (distSq O B) → Equiv (distSq O B) (distSq O C) →
    /// And (Equiv (dot (sub H' A) (sub C B)) zero)
    ///      (Equiv (dot (sub H' B) (sub A C)) zero)`,
    /// where `H' := sub (add (add A B) C) (add O O)`, i.e. `H' := A+B+C−2O`.
    ///
    /// The classical "H, G, O are collinear" statement is false as a property
    /// of arbitrary points satisfying the altitude/equidistance conditions
    /// (degenerate triangles make both hypotheses vacuous for independent
    /// `H`, `O` — see the module-level refutation this theorem replaces).
    /// This is the true, existential form: **given** a circumcentre `O` (the
    /// two equidistance hypotheses), the SPECIFIC point `H' := A+B+C−2O`
    /// satisfies both altitude conditions unconditionally, so it — not an
    /// arbitrary `H` — is the orthocentre. Proved by the per-coordinate
    /// telescope `(A+B+C−2O) − X ~ (Y−O)+(Z−O)` (`Y,Z` the other two
    /// vertices, `h_prime_minus_vertex_scalar_proof`) composed with
    /// `point_diff_diff_fact`'s `Z−Y ~ (Z−O)−(Y−O)`/`Y−Z ~ (Y−O)−(Z−O)`,
    /// then `dot_sub_left`/`dot_sub_right`/`dot_comm` bilinearity collapses
    /// each altitude dot product to `distSq O Z − distSq O Y`, which the
    /// hypotheses (directly, and via [`Self::circumcentre_third_distance`])
    /// make zero.
    pub circumcentre_orthocentre_construction: NameId,
    /// **The Euler line, additive form.** `∀ O A B C,
    /// CPoint.Equiv (add H' (add O O)) (add (add G G) G)`, `H'` as in
    /// [`Self::circumcentre_orthocentre_construction`], `G := centroid A B C`
    /// — i.e. `H' + 2O ~ 3G`, the classical "`HG : GO = 2 : 1`" collinearity
    /// in additive (no division, no ordering) form.
    ///
    /// Unconditional, and purely definitional once `H'` is unfolded: `H' + 2O
    /// ~ A+B+C` by straight cancellation (adding back what `H'` subtracted),
    /// and `A+B+C ~ 3G` is `triple_g_eq_sum_proof` reassociated. Together
    /// with [`Self::circumcentre_orthocentre_construction`] (which exhibits
    /// this *same* `H'` as an orthocentre when `O` is a circumcentre), this
    /// is the Euler line: the orthocentre, centroid and circumcentre of any
    /// triangle are related by `H + 2O ~ 3G`.
    pub euler_line: NameId,
    /// **`BM² = ¼BC²`.** `∀ B C,
    /// Equiv (distSq B (point_midpoint B C)) (mul inv2 (mul inv2 (distSq B C)))`.
    ///
    /// The bridge [`Self::apollonius_from_stewart`] needs: `B − M ~ inv2·(B−C)`
    /// per coordinate (`B` telescoped via `half_double_proof` and `M`'s own
    /// `left_distrib` unfolding), then `sq_scale_proof`'s `(t·x)² ~
    /// t·(t·x²)` pulls both `inv2` factors out of the squared coordinate sum.
    pub midpoint_dist_sq_quarter: NameId,
    /// **`apollonius_median`, re-derived from `stewart_median`.** Same
    /// statement as [`Self::apollonius_median`] — `∀ A B C,
    /// Equiv (add (distSq A B) (distSq A C))
    ///       (add (add (distSq A M) (distSq A M)) (add (distSq B M) (distSq B M)))`
    /// — but proved by doubling [`Self::stewart_median`] and eliminating
    /// `distSq B M` via [`Self::midpoint_dist_sq_quarter`], **not** by
    /// re-running `declare_apollonius_median`'s own route. The two
    /// theorems were previously proved by independent algebra with nothing
    /// connecting them; this is the bridge, landed under its own name rather
    /// than replacing either.
    pub apollonius_from_stewart: NameId,
    /// **Positive-semidefiniteness of `dot`.** `∀ V, CReal.le CReal.zero (dot
    /// V V)`. From `sq_nonneg` on each coordinate plus `add_le_add` — the
    /// first inequality this file proves about `dot`, and the one everything
    /// below needs.
    pub dot_self_nonneg: NameId,
    /// **Lagrange's identity, in the plane.** `∀ a b c e : CReal,
    /// Equiv (add (mul (add (mul a a)(mul b b))(add (mul c c)(mul e e)))
    ///            (neg (mul (add (mul a c)(mul b e))(add (mul a c)(mul b e)))))
    ///       (mul (add (mul a e)(neg (mul b c)))(add (mul a e)(neg (mul b c))))`
    /// — `(a²+b²)(c²+e²) − (ac+be)² = (ae−bc)²`. Pure ring algebra: the
    /// difference is exactly `(ae−bc)²`, `Lagrange's` identity for two pairs
    /// of scalars. [`CPointPrelude::cauchy_schwarz`] is this plus
    /// `sq_nonneg`.
    pub lagrange_identity: NameId,
    /// **Cauchy–Schwarz, squared.** `∀ U V,
    /// CReal.le (mul (dot U V)(dot U V)) (mul (dot U U)(dot V V))`.
    ///
    /// Stated squared and deliberately not as `|⟨u,v⟩| ≤ ‖u‖·‖v‖`: at the
    /// time this was proved, the kernel had `CReal.natSqrt` but no
    /// `CReal.sqrt`, so the norm form was not expressible, let alone
    /// provable, here. `CReal.sqrt` landed 2026-08-26 and the unsquared
    /// form is now proved as `Metric.CPoint.dotLeSqrtMul` in `metric.rs`
    /// (2026-09-04), built on top of this squared statement plus
    /// `CReal.sqrt_mul` — see [`Self::norm`]'s field for the `norm`
    /// definition that makes it statable. The squared form here is what
    /// `lagrange_identity_scalar_proof` plus [`CPointPrelude::dot_self_nonneg`]
    /// (via `le_of_sub_nonneg`) actually delivers, and it is
    /// equivalent-modulo-`sqrt` to the familiar statement.
    pub cauchy_schwarz: NameId,
    /// **The triangle inequality for `distSq`, factor-2 form.** `∀ A B C,
    /// CReal.le (distSq A C) (add (add (distSq A B)(distSq B C)) (add (distSq A B)(distSq B C)))`
    /// — `distSq A C ≤ 2·(distSq A B + distSq B C)`.
    ///
    /// **Not** the classical `d(A,C) ≤ d(A,B) + d(B,C)`: that statement is
    /// about unsquared distances, and squaring it is not equivalent. This
    /// file has no `CReal.sqrt`-based unsquared `distSq` bound built on top
    /// of it — see [`Self::cauchy_schwarz`]'s doc comment for
    /// `Metric.CPoint.dotLeSqrtMul` (`metric.rs`), and `Metric.CPoint.distTriangle`
    /// there for the actual unsquared triangle inequality. This is
    /// the honest reachable
    /// statement, from `(x+y)² ≤ 2(x²+y²)` (`sq_nonneg (x−y)`) applied to
    /// `dot`-vectors via [`Self::dot_self_nonneg`] and [`Self::dot_self_sub`]
    /// rather than per-coordinate — named for exactly what it is, not
    /// `triangle_inequality`.
    pub dist_sq_double_sum_bound: NameId,
    /// **Euclid I.20, squared — the honest triangle inequality.** `∀ A B C,
    /// CReal.le (mul diff diff) (add ab_bc (add ab_bc (add ab_bc ab_bc)))`
    /// where `diff = add (add (distSq A C) (neg (distSq A B))) (neg (distSq
    /// B C))` and `ab_bc = mul (distSq A B) (distSq B C)` — i.e.
    /// `(distSq A C − distSq A B − distSq B C)² ≤ 4 · distSq A B · distSq B C`.
    ///
    /// Unlike [`Self::dist_sq_double_sum_bound`], this **is** equivalent
    /// (modulo `CReal.sqrt`, which now exists — landed 2026-08-26, but is
    /// not applied here) to the classical `|AC| ≤ |AB| +
    /// |BC|`: squaring `|AC| ≤ |AB|+|BC|` and its reverse-triangle
    /// counterpart `||AB|−|BC|| ≤ |AC|` and combining both directions gives
    /// exactly `(distSq A C − distSq A B − distSq B C)² ≤ 4·distSq A B·distSq
    /// B C`, with equality iff `B` lies on segment `AC` (Euclid's actual
    /// content — a straight line is the shortest path). With `U := sub A B`,
    /// `V := sub B C`, the identity `distSq A C − distSq A B − distSq B C ~
    /// dot U V + dot U V` is exact (a ring identity via
    /// [`Self::dot_self_add`], no inequality involved), and squaring it
    /// against [`Self::cauchy_schwarz`] (`dot U V · dot U V ≤ dot U U · dot V
    /// V = distSq A B · distSq B C`) is the whole proof — no square root
    /// needed anywhere, same as [`Self::dist_sq_double_sum_bound`].
    pub dist_sq_triangle_sq_bound: NameId,
    /// **Positive-definiteness of `dot`, converse half.** `∀ V,
    /// CPoint.Equiv V (CPoint.mk CReal.zero CReal.zero) → Equiv (dot V V)
    /// CReal.zero`.
    ///
    /// The cheap direction: from `V`'s coordinates each `Equiv`-zero,
    /// `mul_congr`/`add_congr` push the fact through `dot V V = x V·x V +
    /// y V·y V` to `zero·zero + zero·zero`, and `mul_zero`/`add_zero` collapse
    /// that to `zero`. See [`Self::dot_self_zero_iff`] for the combined
    /// biconditional, and `Complex.normSq_eq_zero_of_eq_zero` in `complex.rs`
    /// for the sibling proof this one mirrors coordinate-for-coordinate.
    pub dot_self_zero_of_eq_zero: NameId,
    /// **Positive-definiteness of `dot`, forward half — the content.** `∀ V,
    /// Equiv (dot V V) CReal.zero → CPoint.Equiv V (CPoint.mk CReal.zero
    /// CReal.zero)`.
    ///
    /// `dot V V ~ 0` is `x V·x V + y V·y V ~ 0` by defeq, both summands
    /// `CReal.sq_nonneg`-nonnegative, so
    /// [`CRealPrelude::eq_zero_of_add_eq_zero_of_nonneg`](crate::CRealPrelude::eq_zero_of_add_eq_zero_of_nonneg)
    /// (applied once directly and once after `add_comm` swaps the summand
    /// order) gives each square `Equiv`-zero, and
    /// [`CRealPrelude::eq_zero_of_mul_self_zero`](crate::CRealPrelude::eq_zero_of_mul_self_zero)
    /// closes each coordinate. Mirrors
    /// `Complex.eq_zero_of_normSq_eq_zero` in `complex.rs`, with the local
    /// `nonneg_sum_zero_left` helper that file needed replaced by the kernel
    /// theorem `eq_zero_of_add_eq_zero_of_nonneg` this development added to
    /// `creal/order_extra.rs`.
    pub eq_zero_of_dot_self_zero: NameId,
    /// **Positive-definiteness of `dot`, the full biconditional.** `∀ V,
    /// Iff (Equiv (dot V V) CReal.zero) (CPoint.Equiv V (CPoint.mk CReal.zero
    /// CReal.zero))`, from [`Self::eq_zero_of_dot_self_zero`] (`mp`) and
    /// [`Self::dot_self_zero_of_eq_zero`] (`mpr`) — a restatement, not a new
    /// proof, in the style [`Self::pythagoras_dist_sq`] uses.
    ///
    /// With this, `dot` satisfies all three inner-product axioms:
    /// symmetry ([`Self::dot_comm`]), bilinearity (the `dot_add_*`/`dot_sub_*`
    /// family), and positive-definiteness (this one) — with
    /// [`Self::cauchy_schwarz`] proved on top.
    pub dot_self_zero_iff: NameId,
    /// **Identity of indiscernibles, converse half.** `∀ A B,
    /// CPoint.Equiv A B → Equiv (distSq A B) CReal.zero`.
    ///
    /// A specialization of [`Self::dot_self_zero_of_eq_zero`] at `V := sub A
    /// B`: componentwise, `Equiv (x A) (x B)` gives `Equiv (add (x A) (neg
    /// (x B))) CReal.zero` (a ring fact, not `CReal`-specific — see the local
    /// `sub_eq_zero_of_equiv` helper), which is exactly `CPoint.Equiv (sub A
    /// B) (mk zero zero)` per coordinate.
    pub dist_sq_eq_zero_of_equiv: NameId,
    /// **Identity of indiscernibles, forward half — the content.** `∀ A B,
    /// Equiv (distSq A B) CReal.zero → CPoint.Equiv A B`.
    ///
    /// A specialization of [`Self::eq_zero_of_dot_self_zero`] at `V := sub A
    /// B`, read back through the local `equiv_of_sub_eq_zero` helper (`add u
    /// (neg v) ~ 0 → u ~ v`, from `sub_add_cancel_proof` and
    /// `zero_add_proof`, both already in this file).
    pub eq_zero_of_dist_sq_eq_zero: NameId,
    /// **Identity of indiscernibles, the full biconditional.** `∀ A B,
    /// Iff (Equiv (distSq A B) CReal.zero) (CPoint.Equiv A B)`, from
    /// [`Self::eq_zero_of_dist_sq_eq_zero`] (`mp`) and
    /// [`Self::dist_sq_eq_zero_of_equiv`] (`mpr`) — a restatement, in the
    /// same style as [`Self::dot_self_zero_iff`].
    ///
    /// With [`Self::dist_sq_comm`] (symmetry) and
    /// [`Self::dist_sq_double_sum_bound`] (the reachable triangle-inequality
    /// substitute — see that field's doc: the classical unsquared form was
    /// not expressible until `CReal.sqrt` landed 2026-08-26, and it is not
    /// built on `distSq` here — see `metric.rs`'s `Metric.CPoint.distTriangle`
    /// for the unsquared route), `distSq` is as much of a metric space
    /// as this file states directly.
    /// [`Self::dist_sq_self_zero`] already gave the `A = B` direction of
    /// this; this is the general biconditional.
    pub dist_sq_eq_zero_iff: NameId,
    /// `CPoint.OnPerpBisector P A B := Equiv (distSq P A) (distSq P B)` — `P`
    /// lies on the perpendicular bisector of segment `AB` iff it is
    /// equidistant (squared) from `A` and `B`.
    pub on_perp_bisector: NameId,
    /// `CPoint.perp_bisector_midpoint : ∀ A B,
    /// OnPerpBisector (point_midpoint A B) A B` — the midpoint of a segment
    /// lies on its own perpendicular bisector.
    pub perp_bisector_midpoint: NameId,
    /// **The perpendicular-bisector characterisation.** `∀ P A B,
    /// Iff (OnPerpBisector P A B)
    ///     (Equiv (dot (sub P (point_midpoint A B)) (sub B A)) CReal.zero)`.
    ///
    /// This is what makes the perpendicular bisector *perpendicular*: `P` is
    /// equidistant from `A` and `B` iff the vector from the midpoint to `P`
    /// is orthogonal to `AB` itself (`dot ~ 0`).
    pub perp_bisector_iff_dot: NameId,
    /// `CPoint.OnCircle P O r2 := Equiv (distSq P O) r2` — the circle of
    /// (squared) radius `r2` centred at `O`, as a locus of points. `r2` is a
    /// bare `CReal`, not asserted nonnegative — at the time this was
    /// defined the kernel had no `CReal.sqrt`, so `r2` could not be related
    /// to an actual radius. `CReal.sqrt` landed 2026-08-26, but this
    /// definition was never rebuilt around it, so `r2` is still never an
    /// actual radius squared *of* anything unless a hypothesis elsewhere
    /// supplies one.
    pub on_circle: NameId,
    /// **A circumcentre lies on all three perpendicular bisectors.** `∀ O A B
    /// C, Equiv (distSq O A) (distSq O B) → Equiv (distSq O B) (distSq O C) →
    /// And (OnPerpBisector O A B) (And (OnPerpBisector O B C) (OnPerpBisector
    /// O A C))`.
    ///
    /// The geometric reading of [`Self::circumcentre_identity`] /
    /// [`Self::circumcentre_third_distance`]: `OnPerpBisector` unfolds to
    /// exactly the equidistance hypotheses/conclusion those already supply.
    pub circumcentre_on_perp_bisectors: NameId,
    /// **Elements III.31, the converse — the headline.** `∀ A B P,
    /// Equiv (dot (sub A P) (sub B P)) CReal.zero →
    /// Equiv (distSq P (point_midpoint A B)) (distSq A (point_midpoint A B))`.
    ///
    /// If the angle at `P` subtended by `AB` is right, `P` lies on the circle
    /// with diameter `AB`. Together with [`Self::thales`] (the same
    /// statement's other direction, already proved), this is the full
    /// biconditional form of Thales' theorem / Elements III.31.
    pub thales_converse: NameId,
    /// `CPoint.cross A B C := CReal.add (CReal.mul (sub Bx Ax) (sub Cy By))
    /// (CReal.neg (CReal.mul (sub By Ay) (sub Cx Bx)))` — twice the signed
    /// area of triangle `ABC`, the 2×2 determinant every orientation,
    /// collinearity and area fact in the plane routes through. Definitional,
    /// not asserted: no hypothesis, no `sqrt` (there is none), a bare
    /// `CReal`.
    pub cross: NameId,
    /// `CPoint.cross_self_left : ∀ A B, Equiv (cross A A B) CReal.zero` — one
    /// of the two structurally cheap degenerate cases (the other is
    /// [`Self::cross_self_right`]): repeating the first point collapses both
    /// factors of the first product to `CReal.add_neg`-zero, and the second
    /// product follows it down for the same reason.
    pub cross_self_left: NameId,
    /// `CPoint.cross_self_right : ∀ A B, Equiv (cross A B B) CReal.zero` —
    /// the mirror degenerate case, repeating the *last* point.
    pub cross_self_right: NameId,
    /// **The `B ↔ C` swap negates `cross`.** `∀ A B C,
    /// Equiv (cross A C B) (CReal.neg (cross A B C))`.
    ///
    /// Proved by relating `cross A C B`'s four factors back to `cross A B
    /// C`'s via `telescope_scalar_proof`/`neg_sub_comm_scalar_proof`,
    /// expanding both products with `right_distrib_proof`/
    /// `mul_neg_right_proof`, and cancelling the shared cross term with
    /// `add_middle_swap_proof` — pure ring algebra, no non-degeneracy
    /// hypothesis anywhere. The `A ↔ B` swap is provable the same way but is
    /// not built here (see the module doc / build notes for why only this
    /// one shipped).
    pub cross_swap_bc: NameId,
    /// `CPoint.NonCollinear A B C k := CReal.PosBound (mul (cross A B C)
    /// (cross A B C)) k` — non-collinearity as a **witnessed** predicate,
    /// carrying the modulus `k` that makes `(cross A B C)²` usable as the
    /// input to `CReal.inv`.
    ///
    /// Not `Not (Equiv (cross A B C) CReal.zero)` (unreachable without
    /// Markov's principle: this kernel proves and assumes neither), and not
    /// `CReal.Apart (cross A B C) CReal.zero` either — `CReal.inv` consumes a
    /// `PosBound` proof, not an `Apart` one (see [`CRealPrelude::inv`]'s own
    /// doc: an `Apart`-indexed inverse would have to eliminate a disjunction
    /// into a `Type`, which `Or.rec` does not permit). Squaring is what turns
    /// "the determinant is nonzero" (which could witness either sign) into
    /// something `PosBound` can state at all: `(cross A B C)²` is
    /// nonnegative regardless of the determinant's own sign.
    pub non_collinear: NameId,
    /// **Two circumcentres' difference is orthogonal to every side.** `∀ O
    /// O' A B C, Equiv (distSq O A) (distSq O B) → Equiv (distSq O B) (distSq
    /// O C) → Equiv (distSq O' A) (distSq O' B) → Equiv (distSq O' B) (distSq
    /// O' C) → And (Equiv (dot (sub O O') (sub B A)) CReal.zero) (Equiv (dot
    /// (sub O O') (sub C B)) CReal.zero)`.
    ///
    /// **Unconditional — no non-degeneracy anywhere.** [`Self::circumcentre_on_perp_bisectors`]
    /// applied at `O` and at `O'` gives, via [`Self::perp_bisector_iff_dot`]'s
    /// `mp` half, `dot (O − M) W ~ 0` and `dot (O' − M) W ~ 0` at `M :=
    /// point_midpoint A B`, `W := sub B A` (and the mirror pair at `M :=
    /// point_midpoint B C`, `W := sub C B`). [`Self::dot_sub_left`] expands
    /// both into `dot O W − dot M W ~ 0` and `dot O' W − dot M W ~ 0`; the
    /// shared `dot M W` cancels (`equiv_of_sub_eq_zero`/`sub_eq_zero_of_equiv`,
    /// the same pair [`Self::eq_zero_of_dist_sq_eq_zero`] uses), leaving `dot
    /// O W ~ dot O' W`, and [`Self::dot_sub_left`] again folds that back into
    /// `dot (sub O O') W ~ 0`.
    pub circumcentre_difference_dots: NameId,
    /// **The 2×2 elimination: a vector orthogonal to two non-parallel sides
    /// is annihilated by their determinant.** `∀ V A B C, Equiv (dot V (sub B
    /// A)) CReal.zero → Equiv (dot V (sub C B)) CReal.zero → And (Equiv (mul
    /// (x V) (cross A B C)) CReal.zero) (Equiv (mul (y V) (cross A B C))
    /// CReal.zero)`.
    ///
    /// **The real content, reusable well beyond circumcentres.** `V` is
    /// completely free — nothing here assumes it is a difference of
    /// circumcentres, only that it is orthogonal to `B−A` and to `C−B`.
    /// Unfolding `dot V (sub B A)` via [`Self::dot_sub_right`] and `dot V B`,
    /// `dot V A` (both free-point applications, pure delta) gives the raw
    /// scalar system `vx·(Bx−Ax) + vy·(By−Ay) ~ 0`, `vx·(Cx−Bx) + vy·(Cy−By)
    /// ~ 0` — the same `u,v,w,z` factors `declare_cross`'s own `cross_raw`
    /// builds. Multiplying the first equation by `(Cy−By)` and the second by
    /// `(By−Ay)`, subtracting, and cancelling the shared cross term (`mul
    /// vx u v ~ mul vx z w` after `mul_assoc`/`mul_comm`, the standard
    /// 2×2-determinant elimination) isolates `vx·(cross A B C) ~ 0`; the
    /// mirror combination (multiply by `(Cx−Bx)` and `(Bx−Ax)`) isolates
    /// `vy·(cross A B C) ~ 0`. Proved directly over points (not over six raw
    /// scalars) so it composes with [`Self::circumcentre_difference_dots`]
    /// without any unfolding glue: `V := sub O O'` substitutes straight in.
    pub cross_annihilates_difference: NameId,
    /// **The headline: three non-collinear points determine a unique
    /// circumcentre.** `∀ k A B C O O', NonCollinear A B C k → Equiv (distSq
    /// O A) (distSq O B) → Equiv (distSq O B) (distSq O C) → Equiv (distSq O'
    /// A) (distSq O' B) → Equiv (distSq O' B) (distSq O' C) → CPoint.Equiv O
    /// O'`.
    ///
    /// [`Self::circumcentre_difference_dots`] gives `dot (sub O O') (sub B
    /// A) ~ 0` and `dot (sub O O') (sub C B) ~ 0`; [`Self::cross_annihilates_difference`]
    /// at `V := sub O O'` turns those into `(x (sub O O'))·D ~ 0` and `(y
    /// (sub O O'))·D ~ 0`, `D := cross A B C`. `NonCollinear A B C k` unfolds
    /// (delta) to `PosBound (mul D D) k`, so `CReal.inv (mul D D) k _`
    /// exists; multiplying each equation by `D` and then by that inverse
    /// (`mul_assoc` twice, [`CRealPrelude::mul_inv_cancel`],
    /// [`CRealPrelude::mul_one`]) cancels `D` and leaves `x (sub O O') ~
    /// CReal.zero` and `y (sub O O') ~ CReal.zero` — which
    /// `equiv_of_sub_eq_zero` (the same helper
    /// [`Self::eq_zero_of_dist_sq_eq_zero`] uses, relying on the same `x (sub
    /// P Q)` defeq-to-`add (x P) (neg (x Q))` reduction that theorem already
    /// exercises) reads back as `Equiv (x O) (x O')` and `Equiv (y O) (y
    /// O')`, i.e. `CPoint.Equiv O O'`.
    pub circumcentre_unique: NameId,
    /// `CPoint.power P O r2 := CReal.add (CPoint.distSq P O) (CReal.neg r2)`
    /// — the power of `P` with respect to the circle centred `O` of squared
    /// radius `r2`. Every circle theorem below routes through this.
    pub power: NameId,
    /// **The power vanishes exactly on the circle.** `∀ P O r2,
    /// Iff (Equiv (power P O r2) CReal.zero) (OnCircle P O r2)`.
    pub power_zero_iff_on_circle: NameId,
    /// `power_of_centre : ∀ O r2, Equiv (power O O r2) (CReal.neg r2)` — the
    /// power of the centre itself, from [`Self::dist_sq_self_zero`].
    pub power_of_centre: NameId,
    /// **The radical axis — the headline.** `∀ O1 O2 r1 r2 P,
    /// Iff (Equiv (power P O1 r1) (power P O2 r2))
    ///     (Equiv (dot (sub P (midpoint O1 O2)) (sub O2 O1))
    ///            (mul CPoint.Scalar.inv2 (sub r1 r2)))` — the locus of
    /// points with equal power to two circles is the line through
    /// `midpoint O1 O2` perpendicular to `O2 - O1`. At `r1 ~ r2` the
    /// right-hand constant collapses to `CReal.zero` and this specializes
    /// (with `A := O1, B := O2`) to exactly [`Self::perp_bisector_iff_dot`]:
    /// a genuine generalisation, not a restatement.
    pub radical_axis_iff_dot: NameId,
    /// **The power difference is affine in `P`.** `∀ O1 O2 r1 r2 P,
    /// Equiv (add (power P O1 r1) (neg (power P O2 r2)))
    ///       (add (mul CPoint.Scalar.two (dot P (sub O2 O1))) constant)`,
    /// `constant` built only from `O1, O2, r1, r2` — the algebraic content
    /// behind [`Self::radical_axis_iff_dot`], named separately.
    pub power_difference_linear: NameId,
    /// **A common point of two circles has equal power, hence lies on the
    /// radical axis.** `∀ O1 O2 r1 r2 P, OnCircle P O1 r1 → OnCircle P O2 r2
    /// → Equiv (dot (sub P (midpoint O1 O2)) (sub O2 O1)) (mul
    /// CPoint.Scalar.inv2 (sub r1 r2))` — composes
    /// [`Self::power_zero_iff_on_circle`] (both hypotheses collapse to
    /// `power ~ 0`) with [`Self::radical_axis_iff_dot`] (equal power gives
    /// the radical-axis membership statement itself, not just equal power).
    pub two_circles_meet_on_radical_axis: NameId,
    /// **The nine-point centre lies on the (additive) Euler line.** `∀ O A B
    /// C, CPoint.Equiv (add (add N N) O) (add (add G G) G)`, where `N :=
    /// point_midpoint O H'` (`H'` the [`Self::circumcentre_orthocentre_construction`]
    /// point, `A+B+C-2O`, built inline — this file registers no name for
    /// either `H'` or `N`) and `G := centroid A B C` — i.e. `2N + O ~ 3G`.
    ///
    /// Unconditional (no circumcentre hypothesis: this is a statement about
    /// *the* point `midpoint(O, H')` for an arbitrary `O`, true before `O` is
    /// ever assumed a circumcentre). Derived from
    /// [`Self::euler_line`]'s own `H' + 2O ~ 3G` plus the pure doubling
    /// identity `2·midpoint(O,H') + O ~ H' + 2O` (`double_midpoint_proof` and
    /// `add_assoc`/`add_comm` rearrangement, per coordinate).
    pub nine_point_centre_on_euler_line: NameId,
    /// **The nine-point radius relation, `BC`-midpoint case.** `∀ O A B C,
    /// Equiv (distSq N (point_midpoint B C)) (mul inv2 (mul inv2 (distSq A
    /// O)))`, `N` as in [`Self::nine_point_centre_on_euler_line`] —
    /// unconditional, true for every `O` (not just a circumcentre).
    ///
    /// The squared nine-point-circle radius, computed against the midpoint
    /// of the side opposite `A`: `N − midpoint(B,C) ~ inv2·(A−O)` per
    /// coordinate (built from `h_prime_minus_vertex_scalar_proof` — reused,
    /// not modified — plus a ring cancellation), then squared and factored
    /// via `sq_scale_proof`, the same "quarter" idiom
    /// [`Self::midpoint_dist_sq_quarter`] uses.
    pub nine_point_radius_bc: NameId,
    /// **The nine-point radius relation, `AB`-midpoint case.** `∀ O A B C,
    /// Equiv (distSq N (point_midpoint A B)) (mul inv2 (mul inv2 (distSq C
    /// O)))` — the [`Self::nine_point_radius_bc`] sibling, dropping `C`
    /// instead of `A`. Unconditional, same proof shape.
    pub nine_point_radius_ab: NameId,
    /// **The nine-point circle's easy half, the headline.** `∀ O A B C,
    /// Equiv (distSq O A) (distSq O B) → Equiv (distSq O B) (distSq O C) →
    /// Equiv (distSq N (point_midpoint A B)) (distSq N (point_midpoint B
    /// C))` — given `O` a circumcentre, the midpoints of `AB` and `BC` are
    /// equidistant from `N`. (The third pair, `distSq N (midpoint B C) ~
    /// distSq N (midpoint C A)`, is the same argument with the third
    /// `nine_point_radius_*` sibling not built here — see the module note.)
    ///
    /// Composes [`Self::nine_point_radius_ab`]/[`Self::nine_point_radius_bc`]
    /// (both give a quarter of a squared distance from `O` to a vertex) with
    /// [`Self::circumcentre_third_distance`] and two [`Self::dist_sq_comm`]
    /// flips, which make those two "quarter" targets equal.
    pub nine_point_centre_equidistant: NameId,
    /// **Ceva's theorem, first slice: the `AX`/`BY` cevian pair meets.**
    /// `∀ A B C p q k, PosBound (mul D D) k → CPoint.Equiv (lerp A (lerp B
    /// C p) t) (lerp B (lerp C A q) u)`, `D := (1-q)+p*q`, `t := (1-q)*z`,
    /// `u := p*z`, `z := D * CReal.inv (mul D D) k _` — the point where
    /// cevians `AX` (`X := lerp B C p`) and `BY` (`Y := lerp C A q`) meet,
    /// exhibited explicitly, whenever the ratios `p, q` are witnessed not
    /// to make the two cevians parallel (`D ≠ 0`, squared per
    /// [`Self::non_collinear`]'s own idiom — see that field's doc for why
    /// `PosBound` rather than `Not (Equiv D CReal.zero)`).
    ///
    /// `D` depends only on `p, q`, not on `A, B, C`: no
    /// [`Self::non_collinear`] hypothesis anywhere, and none is needed —
    /// two cevians with given ratios fail to meet iff `D = 0`, whatever the
    /// triangle's own shape. Proved by `rn_ring_proof` (the ported
    /// `complex::ring` decision procedure) discharging the pure polynomial
    /// identity `lerp a (lerp b c p) t − lerp b (lerp c a q) u ~ (D*z −
    /// 1)*(b−a)` per coordinate (verified exactly with `sympy` before being
    /// encoded — see the module note above
    /// `cevian_pair_ax_by_scalar_proof`), then cancelling the correction
    /// term via the `D*z ~ 1` witness.
    pub cevian_pair_meet: NameId,
    /// **Ceva's theorem, exhibiting direction — the headline.** `∀ A B C p
    /// q r k, PosBound (mul D D) k → Equiv (mul p (mul q r)) (mul (1-p)
    /// (mul (1-q) (1-r))) → And (CPoint.Equiv (lerp A X t) (lerp B Y u))
    /// (CPoint.Equiv (lerp B Y u) (lerp C Z v))`, `X := lerp B C p, Y :=
    /// lerp C A q, Z := lerp A B r`, `D, t, u` as in
    /// [`Self::cevian_pair_meet`], `v := (1-p-q+2*p*q)*z`.
    ///
    /// The classical `(BX/XC)*(CY/YA)*(AZ/ZB) = 1` concurrency criterion,
    /// division-free (`BX/XC = p/(1-p)` etc., and the product-equals-one
    /// condition cross-multiplies to `p*q*r ~ (1-p)*(1-q)*(1-r)`) and in
    /// the constructive **exhibiting** direction: the two `And` conjuncts
    /// pin down one common point on all three cevians by transitivity
    /// (`lerp A X t ~ lerp B Y u ~ lerp C Z v`), given explicitly by its
    /// `t, u, v` parameters — not proved by contradiction, and not
    /// asserting a bare existential.
    ///
    /// The first conjunct is exactly [`Self::cevian_pair_meet`] (proved
    /// independently in this file, reused conceptually but not literally
    /// re-applied — this theorem re-derives it inline so its `z, D`
    /// match the second conjunct's by construction, see the module note
    /// above `cevian_pair_ax_by_scalar_proof`). The second needs the
    /// Ceva ratio hypothesis: `cevian_pair_by_cz_scalar_proof` discharges
    /// the pure ring identity `lerp b (lerp c a q) u − lerp c (lerp a b r)
    /// v ~ (D*z−1)*(c−b) + (z*(a−b))*(p*q*r−(1−p)*(1−q)*(1−r))` (again
    /// checked exactly with `sympy` before encoding), and the Ceva
    /// hypothesis is exactly what makes the second summand's `defect`
    /// factor vanish.
    ///
    /// Only `D`'s non-degeneracy is hypothesised (`PosBound (mul D D) k`,
    /// same idiom as [`Self::non_collinear`]) — **no**
    /// [`Self::non_collinear`] hypothesis on `A, B, C` anywhere, since `D`
    /// depends only on `p, q` (see [`Self::cevian_pair_meet`]'s doc). The
    /// converse direction (concurrency implies the ratio product) is
    /// [`Self::ceva_ratio_product_of_concurrent`].
    pub ceva_concurrent_of_ratio_product: NameId,
    /// **Menelaus' theorem, the sign-flipped analogue of
    /// [`Self::ceva_concurrent_of_ratio_product`].** `∀ A B C p q r, Equiv
    /// (mul p (mul q r)) (neg (mul (1-p) (mul (1-q) (1-r)))) → Equiv (cross
    /// X Y Z) CReal.zero`, `X := lerp B C p, Y := lerp C A q, Z := lerp A B
    /// r` — the classical `(BX/XC)*(CY/YA)*(AZ/ZB) = -1` transversal
    /// criterion, division-free, in the **collinear-of-ratio-product**
    /// direction.
    ///
    /// Unlike Ceva, this is a **pure polynomial identity with no
    /// non-degeneracy hypothesis whatsoever**, not even `D ≠ 0`: `cross X Y
    /// Z ~ (mul p (mul q r) + mul (1-p) (mul (1-q) (1-r))) * cross A B C`
    /// holds identically (checked exactly with `sympy`, see the module
    /// note), so when the ratio-product hypothesis makes the left factor
    /// vanish, `cross X Y Z` vanishes regardless of `cross A B C` — even a
    /// degenerate `A, B, C` triangle satisfies the conclusion trivially,
    /// since then `cross A B C` is already `~ 0`.
    pub menelaus_collinear_of_ratio_product: NameId,
    /// **Ceva's theorem, the converse: concurrency implies the ratio
    /// product.** `∀ A B C p q r k k2, PosBound (mul D D) k → PosBound
    /// (distSq A B) k2 → CPoint.Equiv (lerp B Y u) (lerp C Z v) → Equiv (mul
    /// p (mul q r)) (mul (1-p) (mul (1-q) (1-r)))`, `D, Y, Z, u, v` as in
    /// [`Self::ceva_concurrent_of_ratio_product`].
    ///
    /// Two non-degeneracy hypotheses the exhibiting direction did not need:
    /// `D ≠ 0` (so the canonical `BY`/`CZ` parametrisation via `z := D⁻¹`
    /// is available at all — the same witnessed-squared idiom as
    /// [`Self::cevian_pair_meet`]) and `A ≠ B` (`distSq A B` witnessed
    /// `PosBound`, since `cevian_pair_by_cz_scalar_proof`'s ring identity
    /// puts the Ceva defect on a factor of `(x A − x B)` and `(y A − y B)`
    /// jointly — if `A ~ B` the concurrency hypothesis carries no
    /// information about the defect at all).
    ///
    /// Route: the same ring identity `cevian_pair_by_cz_scalar_proof`
    /// discharges (`lerp b Y u − lerp c Z v ~ (D*z−1)*(c−b) +
    /// (z*(a−b))*defect`) runs in reverse — the hypothesis makes the left
    /// side `~ 0`, the first summand is `~ 0` unconditionally (from `D*z ~
    /// 1`), so the second summand is `~ 0`; multiplying through by `D`
    /// cancels the shared `z` factor via `D*z ~ 1` (no need for `z` to be
    /// independently invertible), leaving `(a−b)*defect ~ 0` at **both**
    /// coordinates. Squaring and summing the two gives `distSq A B *
    /// defect² ~ 0`; `distSq A B` invertible (from `PosBound`) cancels it to
    /// `defect² ~ 0`, and `eq_zero_of_mul_self_zero` finishes at `defect ~
    /// 0`, i.e. the Ceva ratio equation.
    pub ceva_ratio_product_of_concurrent: NameId,
    /// **Heron's formula, squared -- no `CReal.sqrt` needed anywhere.** `∀ A
    /// B C, Equiv (mul (add cross cross) (add cross cross)) (add (mul (add
    /// a2 a2) (add b2 b2)) (neg (mul diff diff)))`, `cross := CPoint.cross A
    /// B C`, `a2 := distSq B C`, `b2 := distSq C A`, `c2 := distSq A B`,
    /// `diff := add a2 (add b2 (neg c2))`.
    ///
    /// `cross` is [`Self::cross`]'s own doc: twice the *signed* area of
    /// triangle `ABC`. So `add cross cross` is `4*Area`, and the left side is
    /// `16*Area^2` -- the theorem is `16*Area^2 = 4a^2b^2 - (a^2+b^2-c^2)^2`
    /// written division-free (`add x x` rather than `mul CPoint.Scalar.two
    /// x`, purely to avoid a second folded constant in the statement). No
    /// hypothesis, for every configuration of `A, B, C`, degenerate or not --
    /// squaring away the sign of `cross` is exactly what makes that
    /// possible.
    ///
    /// **Unconditional pure ring algebra**, verified exactly over the six raw
    /// coordinates before being encoded (`Fraction` trials, zero residual --
    /// no `sympy` in this environment): `heron_scalar_proof` builds `cross`
    /// via `rn_cross` (the same `RnExpr` mirror of `cross_raw` the
    /// Menelaus/Ceva development already established) and each `a^2`/`b^2`/
    /// `c^2` via the new `rn_dist_sq` (the analogous mirror of
    /// [`Self::dist_sq`]'s own delta/iota unfolding through `dot`, `sub`, and
    /// the `x`/`y` projections of `sub`'s `mk` constructor -- precedent for
    /// the kernel accepting exactly this depth already exists in this file:
    /// `declare_dist_sq_self_zero`'s own `sum` local is the same shape at
    /// `P = Q`), then discharges the resulting six-variable identity with
    /// `rn_ring_proof`.
    pub heron_sixteen_area_sq: NameId,
    /// **Translation invariance of `cross`.** `∀ A B C V,
    /// Equiv (cross (add A V) (add B V) (add C V)) (cross A B C)`.
    ///
    /// Unconditional pure ring algebra, discharged directly by
    /// `rn_ring_proof` over the eight raw coordinates `Ax,Ay,Bx,By,Cx,Cy,Vx,Vy`
    /// -- no squaring anywhere (unlike [`Self::heron_sixteen_area_sq`]), so
    /// this is nowhere near the ring normalizer's size ceiling. The stated
    /// type uses `CPoint.add`; the kernel accepts the raw-coordinate proof
    /// against it by delta/iota-unfolding `add`'s `mk`-coordinatewise
    /// definition (`x (add P Q) ~delta/iota~> add (x P) (x Q)`), the same
    /// unfolding depth [`Self::cross`] itself, and every `cross`-headed
    /// theorem in this file, already relies on.
    pub cross_translate: NameId,
    /// `CPoint.Collinear A B C := Exists CReal (fun t => CPoint.Equiv C
    /// (CPoint.lerp A B t))` -- the classical "C lies on line AB" predicate,
    /// stated with the SAME parametrisation [`Self::cevian_pair_meet`]'s `X :=
    /// lerp B C p` idiom uses everywhere else in this file, not a bare
    /// three-point determinant condition. Definitional, not asserted.
    ///
    /// Chosen as an existential (not, say, "`cross A B C ~ 0`" itself) because
    /// that is the classical statement of collinearity and lets
    /// [`Self::area_zero_of_collinear`] be a genuine theorem *about* it rather
    /// than a restatement; see that field's doc for why only this one
    /// direction is built here.
    pub collinear: NameId,
    /// **One direction of "signed area vanishes iff collinear".** `∀ A B C,
    /// Collinear A B C → Equiv (cross A B C) CReal.zero`.
    ///
    /// This is the direction actually reachable without classical logic:
    /// `Collinear A B C` is an `Exists`, and `Exists.rec` (`Exists` is `Prop`
    /// with one non-subsingleton constructor) eliminates into any `Prop`
    /// target -- which `Equiv (cross A B C) CReal.zero` already is, so
    /// consuming the hypothesis needs no witness extraction. Given the
    /// witness `t` and `hC : CPoint.Equiv C (lerp A B t)`: `cross A B (lerp A
    /// B t) ~ CReal.zero` is a pure ring identity with NO hypothesis (a point
    /// on segment `AB` is always collinear with `A, B` -- verified exactly
    /// with `Fraction` trials before encoding, no `sympy` in this
    /// environment), and `hC` transports `cross A B C ~ cross A B (lerp A B
    /// t)` through a hand-built third-argument congruence for `cross`
    /// (`cross`'s definition is not built from `dot`/`sub` the way
    /// [`Self::dist_sq`] is, so it needs its own congruence chain through
    /// `add_congr`/`mul_congr`/`neg_congr` rather than reusing
    /// [`Self::dot_congr`]).
    ///
    /// **The converse (`cross A B C ~ 0 → Collinear A B C`) is NOT built
    /// here.** It needs a witness `t` *constructed*, and `Exists.rec`'s
    /// eliminator cannot supply one when the target is `Type`-valued (the
    /// module doc's standing "`Exists`'s witness is not exposed by
    /// `Exists.rec`" constraint -- see `creal.rs`'s own note at
    /// [`CRealPrelude::inv`]). It is also not simply true without a
    /// non-degeneracy hypothesis: at `A ~ B`, `cross A B C ~ 0` holds for
    /// EVERY `C` (both raw factors collapse), while `Collinear A B C` at `A ~
    /// B` forces `C ~ A` (`lerp A A t ~ A` for every `t`) -- so the bare iff
    /// is false, not merely hard, and a witnessed `A ≠ B` hypothesis (the
    /// [`Self::non_collinear`]-style `PosBound (distSq A B) k` idiom) would be
    /// needed to state and prove it honestly. Left for a later slice.
    pub area_zero_of_collinear: NameId,
    /// **The medial triangle's (signed) area is a quarter of the original.**
    /// `∀ A B C, Equiv (cross Ma Mb Mc) (mul inv2 (mul inv2 (cross A B C)))`,
    /// `Ma := midpoint B C, Mb := midpoint C A, Mc := midpoint A B`.
    ///
    /// Stated as `mul inv2 (mul inv2 …)` rather than "divide `cross A B C` by
    /// a `Nat`-built `4`" -- the same idiom [`Self::midpoint_dist_sq_quarter`]
    /// and the `nine_point_radius_*` pair already use for a squared-midpoint
    /// quarter -- because it is what makes the identity a PURE ring fact: an
    /// `inv2` from each of two coordinate differences of midpoints multiplies
    /// into an `inv2·inv2` factor on the left exactly matching the two
    /// literal `inv2` factors on the right, so `rn_ring_proof` discharges it
    /// treating `inv2` as an opaque atom -- **no fact that `inv2` numerically
    /// denotes `1/2` (e.g. `mul two inv2 ~ one`) is used anywhere in this
    /// proof.** Verified first over generic `h` in place of `inv2` (not fixed
    /// at `1/2`) with `Fraction` trials: `cross(h·(B+C), h·(C+A), h·(A+B)) =
    /// h²·cross(A,B,C)` identically, confirming it really is a ring identity
    /// and not a numerical coincidence at `h = 1/2`. Only 6 monomials survive
    /// cancellation on each side (checked with the same trial script) -- far
    /// below the size that made a flat `rn_ring_proof` SIGABRT for
    /// [`Self::heron_sixteen_area_sq`]'s first attempt, so this needed no
    /// staging.
    pub medial_triangle_cross_quarter: NameId,
    /// **The converse of [`Self::area_zero_of_collinear`], under a witnessed
    /// non-degeneracy hypothesis.** `∀ A B C k, PosBound (distSq A B) k →
    /// Equiv (cross A B C) CReal.zero → Collinear A B C`.
    ///
    /// The hypothesis is unavoidable, not merely convenient: at `A ~ B`,
    /// `cross A B C ~ 0` holds for every `C` (see
    /// [`Self::area_zero_of_collinear`]'s own doc), so the bare "cross zero
    /// implies collinear" is false, and `PosBound (distSq A B) k` is exactly
    /// the [`Self::non_collinear`]-style witnessed idiom for `A ≠ B`.
    ///
    /// **The construction, on paper.** Write `u := B − A`, `v := C − A`
    /// (per coordinate). `cross A B C ~ 0` is `u₁v₂ − u₂v₁ ~ 0`
    /// (`cross_raw`'s formula reduces to exactly this after the `u₁u₂` cross
    /// terms cancel -- checked with `Fraction` trials, not re-derived by the
    /// kernel, which only ever sees the un-reduced `cross_raw` shape). The
    /// projection parameter `t := (v·u) · (distSq A B)⁻¹` (`distSq A B`
    /// invertible from the hypothesis) satisfies, as a PURE ring identity
    /// with no hypothesis at all: `v₁·distSq A B ~ (v·u)·u₁ − u₂·(cross A B
    /// C)` and its `v₂` mirror with `+u₁·(cross A B C)` -- both verified
    /// exactly with `Fraction` trials before encoding. `cross A B C ~ 0`
    /// (the theorem's hypothesis) kills the correction term in each, leaving
    /// `v₁·distSq A B ~ (v·u)·u₁`; cancelling the invertible `distSq A B`
    /// gives `v₁ ~ t·u₁`, i.e. `Cx − Ax ~ t·(Bx − Ax)`, i.e. exactly `Cx ~ x
    /// (lerp A B t)` -- and the `y` mirror -- which is
    /// `CPoint.Equiv C (lerp A B t)`, the witness `Collinear A B C` needs.
    ///
    /// Built from small reusable pieces (`eliminate_correction_proof`,
    /// `divide_by_pos_bound_proof`) rather than one flat chain -- the same
    /// staging discipline [`Self::heron_sixteen_area_sq`]'s own doc
    /// describes, applied here to proof-term SHAPE rather than ring-normal-
    /// form size.
    pub collinear_of_area_zero: NameId,

    // --- angle measure (creal_point/angle.rs) --------------------------------
    /// `CPoint.norm : CPoint → CReal := fun V => CReal.sqrt (CPoint.dot V V)`.
    ///
    /// The unsquared length, expressible because `CReal.sqrt` exists — several
    /// doc comments above still say it does not, and they are stale.
    pub norm: NameId,
    /// `CPoint.norm_nonneg : ∀ V, CReal.le CReal.zero (norm V)`.
    pub norm_nonneg: NameId,
    /// `CPoint.norm_sq : ∀ V, Equiv (mul (norm V) (norm V)) (dot V V)` —
    /// `mul_self_sqrt` discharged by [`Self::dot_self_nonneg`].
    pub norm_sq: NameId,
    /// `CPoint.norm_congr : ∀ U V, CPoint.Equiv U V → Equiv (norm U) (norm V)`.
    pub norm_congr: NameId,
    /// `CPoint.crossV U V := add (mul (x U) (y V)) (neg (mul (y U) (x V)))` —
    /// the two-vector determinant, the `dot`-sibling the file never had (the
    /// existing [`Self::cross`] takes three POINTS).
    pub cross_v: NameId,
    /// `CPoint.cross_eq_crossV : ∀ A B C,
    /// Equiv (cross A B C) (crossV (sub B A) (sub C B))` — `equiv_refl`. The
    /// triangle determinant IS the vector cross product at the two edge
    /// vectors, definitionally, so every existing `cross` theorem transports
    /// to the angle layer for free.
    pub cross_eq_cross_v: NameId,
    /// `CPoint.lagrange_vector : ∀ U V,
    /// Equiv (add (mul (dot U U) (dot V V)) (neg (mul (dot U V) (dot U V))))
    ///       (mul (crossV U V) (crossV U V))` — `‖u‖²‖v‖² − ⟨u,v⟩² = (u×v)²`,
    /// [`Self::lagrange_identity`] at the four coordinates and nothing else.
    /// **This is the Pythagorean identity for the angle**, before dividing by
    /// `‖u‖²‖v‖²`.
    pub lagrange_vector: NameId,
    /// `CPoint.law_of_cosines_dot : ∀ U V,
    /// Equiv (distSq U V) (add (add (dot U U) (dot V V)) (neg (add (dot U V) (dot U V))))`
    /// — `‖u−v‖² = ‖u‖² + ‖v‖² − 2⟨u,v⟩`, [`Self::dot_self_sub`] regrouped.
    pub law_of_cosines_dot: NameId,
    /// `CPoint.cosAngle : (U V : CPoint) → (k : Nat) →
    /// PosBound (mul (norm U) (norm V)) k → CReal`
    /// `:= mul (dot U V) (inv (mul (norm U) (norm V)) k h)`.
    ///
    /// The modulus is data, exactly as in [`Self::non_collinear`]: `CReal.inv`
    /// consumes a `PosBound`, not an `Apart`.
    pub cos_angle: NameId,
    /// `CPoint.sinAngle : … → CReal
    /// := mul (abs (crossV U V)) (inv (mul (norm U) (norm V)) k h)` — the
    /// UNSIGNED sine; a signed one would need a decision on the sign of a real.
    pub sin_angle: NameId,
    /// `CPoint.sin_sq_add_cos_sq : ∀ U V k h,
    /// Equiv (add (mul (sinAngle …) (sinAngle …)) (mul (cosAngle …) (cosAngle …)))
    ///       CReal.one`.
    ///
    /// **The Pythagorean identity, with no trigonometry in it** —
    /// [`Self::lagrange_vector`] divided by `‖u‖²‖v‖²`. `CReal` has no
    /// `sin_sq_add_cos_sq` of its own (checked 2026-09-04), and this does not
    /// need one.
    pub sin_sq_add_cos_sq: NameId,
    /// `CPoint.abs_cos_angle_le_one : ∀ U V k h, le (abs (cosAngle …)) one` —
    /// unsquared Cauchy–Schwarz, read off [`Self::sin_sq_add_cos_sq`].
    pub abs_cos_angle_le_one: NameId,
    /// `CPoint.cos_angle_le_one : ∀ U V k h, le (cosAngle …) CReal.one`.
    pub cos_angle_le_one: NameId,
    /// `CPoint.neg_one_le_cos_angle : ∀ U V k h, le (neg CReal.one) (cosAngle …)`
    /// — with [`Self::cos_angle_le_one`], the `[−1, 1]` range an `arccos`
    /// would consume, landed without one.
    pub neg_one_le_cos_angle: NameId,
    /// `CPoint.norm_mul_cos_angle : ∀ U V k h,
    /// Equiv (mul (mul (norm U) (norm V)) (cosAngle …)) (dot U V)`.
    pub norm_mul_cos_angle: NameId,
    /// `CPoint.law_of_sines : ∀ U V k h,
    /// Equiv (abs (crossV U V)) (mul (mul (norm U) (norm V)) (sinAngle …))` —
    /// `|u × v| = ‖u‖ ‖v‖ sin θ`.
    pub law_of_sines: NameId,
    /// `CPoint.law_of_cosines : ∀ U V k h,
    /// Equiv (distSq U V) (‖u‖² + ‖v‖² − 2‖u‖‖v‖ cos θ)` — the classical
    /// statement, with `2X` written `X + X`.
    pub law_of_cosines: NameId,

    // --- isometries (creal_point/isometry.rs) --------------------------------
    /// `CPoint.Isometry f := ∀ P Q, Equiv (distSq (f P) (f Q)) (distSq P Q)`.
    pub isometry: NameId,
    /// `CPoint.idMap := fun P => P`.
    pub id_map: NameId,
    /// `CPoint.comp f g := fun P => f (g P)`.
    pub comp_map: NameId,
    /// `CPoint.isometry_id : Isometry idMap`.
    pub isometry_id: NameId,
    /// `CPoint.isometry_comp : ∀ f g, Isometry f → Isometry g →
    /// Isometry (comp f g)`. With [`Self::isometry_id`], the monoid
    /// structure; inverses need surjectivity, which the predicate does not
    /// carry.
    pub isometry_comp: NameId,
    /// `CPoint.translate T := fun P => CPoint.add P T`.
    pub translate: NameId,
    /// `CPoint.isometry_translate : ∀ T, Isometry (translate T)` — no
    /// hypothesis at all.
    pub isometry_translate: NameId,
    /// `CPoint.rotate c s := fun P => mk (c·Px − s·Py) (s·Px + c·Py)` —
    /// parameterised by the PAIR, never by an angle.
    pub rotate: NameId,
    /// `CPoint.isometry_rotate : ∀ c s, Equiv (add (mul c c) (mul s s)) one →
    /// Isometry (rotate c s)`.
    pub isometry_rotate: NameId,
    /// `CPoint.reflect c s := fun P => mk (c·Px + s·Py) (s·Px − c·Py)`.
    pub reflect: NameId,
    /// `CPoint.isometry_reflect : ∀ c s, Equiv (add (mul c c) (mul s s)) one →
    /// Isometry (reflect c s)`.
    pub isometry_reflect: NameId,
    /// `CPoint.scale r := fun P => mk (r·Px) (r·Py)`.
    pub scale: NameId,
    /// `CPoint.scale_distSq : ∀ r P Q,
    /// Equiv (distSq (scale r P) (scale r Q)) (mul (mul r r) (distSq P Q))` —
    /// the exact scaling law, for every `r`.
    pub scale_dist_sq: NameId,
    /// `CPoint.not_isometry_scale_two : Isometry (scale two) → False`.
    ///
    /// **The negative control, as a theorem.** The doubling map takes
    /// `distSq = 1` to `distSq = 4`; two `add_right_cancel` steps turn `4 ~ 1`
    /// into `1 + 1 ~ −1`, and `CReal.not_le_zero_neg_one` refutes the `0 ≤ −1`
    /// that follows. Constructive, no `Apart`, no case split.
    pub not_isometry_scale_two: NameId,
    /// `CPoint.isometry_preserves_dot : ∀ f, Isometry f → ∀ P Q R,
    /// Equiv (dot (sub (f P) (f R)) (sub (f Q) (f R))) (dot (sub P R) (sub Q R))`
    /// — polarization plus the hypothesis at three pairs, then one halving.
    /// Step 1 of the classification; the remaining three steps are sized in
    /// `creal_point/isometry.rs`'s module doc.
    pub isometry_preserves_dot: NameId,
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
    declare_circumcentre_orthocentre_construction(&mut d, p)?;
    declare_euler_line(&mut d, p)?;
    declare_midpoint_dist_sq_quarter(&mut d, p)?;
    declare_apollonius_from_stewart(&mut d, p)?;
    declare_dot_self_nonneg(&mut d, p)?;
    declare_lagrange_identity(&mut d, p)?;
    declare_cauchy_schwarz(&mut d, p)?;
    declare_dist_sq_double_sum_bound(&mut d, p)?;
    declare_dist_sq_triangle_sq_bound(&mut d, p)?;
    declare_dot_self_zero_of_eq_zero(&mut d, p)?;
    declare_eq_zero_of_dot_self_zero(&mut d, p)?;
    declare_dot_self_zero_iff(&mut d, p)?;
    declare_dist_sq_eq_zero_of_equiv(&mut d, p)?;
    declare_eq_zero_of_dist_sq_eq_zero(&mut d, p)?;
    declare_dist_sq_eq_zero_iff(&mut d, p)?;
    declare_on_perp_bisector(&mut d, p)?;
    declare_perp_bisector_midpoint(&mut d, p)?;
    declare_perp_bisector_iff_dot(&mut d, p)?;
    declare_on_circle(&mut d, p)?;
    declare_circumcentre_on_perp_bisectors(&mut d, p)?;
    declare_thales_converse(&mut d, p)?;
    declare_cross(&mut d, p)?;
    declare_cross_self_left(&mut d, p)?;
    declare_cross_self_right(&mut d, p)?;
    declare_cross_swap_bc(&mut d, p)?;
    declare_non_collinear(&mut d, p)?;
    declare_circumcentre_difference_dots(&mut d, p)?;
    declare_cross_annihilates_difference(&mut d, p)?;
    declare_circumcentre_unique(&mut d, p)?;
    declare_power(&mut d, p)?;
    declare_power_zero_iff_on_circle(&mut d, p)?;
    declare_power_of_centre(&mut d, p)?;
    declare_radical_axis_iff_dot(&mut d, p)?;
    declare_power_difference_linear(&mut d, p)?;
    declare_two_circles_meet_on_radical_axis(&mut d, p)?;
    declare_nine_point_centre_on_euler_line(&mut d, p)?;
    declare_nine_point_radius_bc(&mut d, p)?;
    declare_nine_point_radius_ab(&mut d, p)?;
    declare_nine_point_centre_equidistant(&mut d, p)?;
    declare_cevian_pair_meet(&mut d, p)?;
    declare_ceva_concurrent_of_ratio_product(&mut d, p)?;
    declare_menelaus_collinear_of_ratio_product(&mut d, p)?;
    declare_ceva_ratio_product_of_concurrent(&mut d, p)?;
    declare_heron_sixteen_area_sq(&mut d, p)?;
    declare_cross_translate(&mut d, p)?;
    declare_collinear(&mut d, p)?;
    declare_area_zero_of_collinear(&mut d, p)?;
    declare_medial_triangle_cross_quarter(&mut d, p)?;
    declare_collinear_of_area_zero(&mut d, p)?;
    // --- angle measure (creal_point/angle.rs) ---------------------------------
    angle::declare_norm(&mut d, p)?;
    angle::declare_norm_nonneg(&mut d, p)?;
    angle::declare_norm_sq(&mut d, p)?;
    angle::declare_norm_congr(&mut d, p)?;
    angle::declare_cross_v(&mut d, p)?;
    angle::declare_cross_eq_cross_v(&mut d, p)?;
    angle::declare_lagrange_vector(&mut d, p)?;
    angle::declare_law_of_cosines_dot(&mut d, p)?;
    angle::declare_cos_angle(&mut d, p)?;
    angle::declare_sin_angle(&mut d, p)?;
    angle::declare_sin_sq_add_cos_sq(&mut d, p)?;
    angle::declare_abs_cos_angle_le_one(&mut d, p)?;
    angle::declare_cos_angle_le_one(&mut d, p)?;
    angle::declare_neg_one_le_cos_angle(&mut d, p)?;
    angle::declare_norm_mul_cos_angle(&mut d, p)?;
    angle::declare_law_of_sines(&mut d, p)?;
    angle::declare_law_of_cosines(&mut d, p)?;
    // --- isometries (creal_point/isometry.rs) ---------------------------------
    isometry::declare_isometry(&mut d, p)?;
    isometry::declare_id_map(&mut d, p)?;
    isometry::declare_comp_map(&mut d, p)?;
    isometry::declare_isometry_id(&mut d, p)?;
    isometry::declare_isometry_comp(&mut d, p)?;
    isometry::declare_translate(&mut d, p)?;
    isometry::declare_isometry_translate(&mut d, p)?;
    isometry::declare_rotate(&mut d, p)?;
    isometry::declare_isometry_rotate(&mut d, p)?;
    isometry::declare_reflect(&mut d, p)?;
    isometry::declare_isometry_reflect(&mut d, p)?;
    isometry::declare_scale(&mut d, p)?;
    isometry::declare_scale_dist_sq(&mut d, p)?;
    isometry::declare_not_isometry_scale_two(&mut d, p)?;
    isometry::declare_isometry_preserves_dot(&mut d, p)?;
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
        circumcentre_orthocentre_construction: kernel
            .name_str(point, "circumcentre_orthocentre_construction"),
        euler_line: kernel.name_str(point, "euler_line"),
        midpoint_dist_sq_quarter: kernel.name_str(point, "midpoint_dist_sq_quarter"),
        apollonius_from_stewart: kernel.name_str(point, "apollonius_from_stewart"),
        dot_self_nonneg: kernel.name_str(point, "dot_self_nonneg"),
        lagrange_identity: kernel.name_str(point, "lagrange_identity"),
        cauchy_schwarz: kernel.name_str(point, "cauchy_schwarz"),
        dist_sq_double_sum_bound: kernel.name_str(point, "distSq_double_sum_bound"),
        dist_sq_triangle_sq_bound: kernel.name_str(point, "distSq_triangle_sq_bound"),
        dot_self_zero_of_eq_zero: kernel.name_str(point, "dot_self_zero_of_eq_zero"),
        eq_zero_of_dot_self_zero: kernel.name_str(point, "eq_zero_of_dot_self_zero"),
        dot_self_zero_iff: kernel.name_str(point, "dot_self_zero_iff"),
        dist_sq_eq_zero_of_equiv: kernel.name_str(point, "distSq_eq_zero_of_equiv"),
        eq_zero_of_dist_sq_eq_zero: kernel.name_str(point, "eq_zero_of_distSq_eq_zero"),
        dist_sq_eq_zero_iff: kernel.name_str(point, "distSq_eq_zero_iff"),
        on_perp_bisector: kernel.name_str(point, "OnPerpBisector"),
        perp_bisector_midpoint: kernel.name_str(point, "perp_bisector_midpoint"),
        perp_bisector_iff_dot: kernel.name_str(point, "perp_bisector_iff_dot"),
        on_circle: kernel.name_str(point, "OnCircle"),
        circumcentre_on_perp_bisectors: kernel.name_str(point, "circumcentre_on_perp_bisectors"),
        thales_converse: kernel.name_str(point, "thales_converse"),
        cross: kernel.name_str(point, "cross"),
        cross_self_left: kernel.name_str(point, "cross_self_left"),
        cross_self_right: kernel.name_str(point, "cross_self_right"),
        cross_swap_bc: kernel.name_str(point, "cross_swap_bc"),
        non_collinear: kernel.name_str(point, "NonCollinear"),
        circumcentre_difference_dots: kernel.name_str(point, "circumcentre_difference_dots"),
        cross_annihilates_difference: kernel.name_str(point, "cross_annihilates_difference"),
        circumcentre_unique: kernel.name_str(point, "circumcentre_unique"),
        power: kernel.name_str(point, "power"),
        power_zero_iff_on_circle: kernel.name_str(point, "power_zero_iff_on_circle"),
        power_of_centre: kernel.name_str(point, "power_of_centre"),
        radical_axis_iff_dot: kernel.name_str(point, "radical_axis_iff_dot"),
        power_difference_linear: kernel.name_str(point, "power_difference_linear"),
        two_circles_meet_on_radical_axis: kernel
            .name_str(point, "two_circles_meet_on_radical_axis"),
        nine_point_centre_on_euler_line: kernel.name_str(point, "nine_point_centre_on_euler_line"),
        nine_point_radius_bc: kernel.name_str(point, "nine_point_radius_bc"),
        nine_point_radius_ab: kernel.name_str(point, "nine_point_radius_ab"),
        nine_point_centre_equidistant: kernel.name_str(point, "nine_point_centre_equidistant"),
        cevian_pair_meet: kernel.name_str(point, "cevian_pair_meet"),
        ceva_concurrent_of_ratio_product: kernel
            .name_str(point, "ceva_concurrent_of_ratio_product"),
        menelaus_collinear_of_ratio_product: kernel
            .name_str(point, "menelaus_collinear_of_ratio_product"),
        ceva_ratio_product_of_concurrent: kernel
            .name_str(point, "ceva_ratio_product_of_concurrent"),
        heron_sixteen_area_sq: kernel.name_str(point, "heron_sixteen_area_sq"),
        cross_translate: kernel.name_str(point, "cross_translate"),
        collinear: kernel.name_str(point, "Collinear"),
        area_zero_of_collinear: kernel.name_str(point, "area_zero_of_collinear"),
        medial_triangle_cross_quarter: kernel.name_str(point, "medial_triangle_cross_quarter"),
        collinear_of_area_zero: kernel.name_str(point, "collinear_of_area_zero"),
        norm: kernel.name_str(point, "norm"),
        norm_nonneg: kernel.name_str(point, "norm_nonneg"),
        norm_sq: kernel.name_str(point, "norm_sq"),
        norm_congr: kernel.name_str(point, "norm_congr"),
        cross_v: kernel.name_str(point, "crossV"),
        cross_eq_cross_v: kernel.name_str(point, "cross_eq_crossV"),
        lagrange_vector: kernel.name_str(point, "lagrange_vector"),
        law_of_cosines_dot: kernel.name_str(point, "law_of_cosines_dot"),
        cos_angle: kernel.name_str(point, "cosAngle"),
        sin_angle: kernel.name_str(point, "sinAngle"),
        sin_sq_add_cos_sq: kernel.name_str(point, "sin_sq_add_cos_sq"),
        abs_cos_angle_le_one: kernel.name_str(point, "abs_cos_angle_le_one"),
        cos_angle_le_one: kernel.name_str(point, "cos_angle_le_one"),
        neg_one_le_cos_angle: kernel.name_str(point, "neg_one_le_cos_angle"),
        norm_mul_cos_angle: kernel.name_str(point, "norm_mul_cos_angle"),
        law_of_sines: kernel.name_str(point, "law_of_sines"),
        law_of_cosines: kernel.name_str(point, "law_of_cosines"),
        isometry: kernel.name_str(point, "Isometry"),
        id_map: kernel.name_str(point, "idMap"),
        comp_map: kernel.name_str(point, "comp"),
        isometry_id: kernel.name_str(point, "isometry_id"),
        isometry_comp: kernel.name_str(point, "isometry_comp"),
        translate: kernel.name_str(point, "translate"),
        isometry_translate: kernel.name_str(point, "isometry_translate"),
        rotate: kernel.name_str(point, "rotate"),
        isometry_rotate: kernel.name_str(point, "isometry_rotate"),
        reflect: kernel.name_str(point, "reflect"),
        isometry_reflect: kernel.name_str(point, "isometry_reflect"),
        scale: kernel.name_str(point, "scale"),
        scale_dist_sq: kernel.name_str(point, "scale_distSq"),
        not_isometry_scale_two: kernel.name_str(point, "not_isometry_scale_two"),
        isometry_preserves_dot: kernel.name_str(point, "isometry_preserves_dot"),
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

// --- the Euler line: a circumcentre's construction of an orthocentre -------

/// `Equiv (add (add x (neg y)) y) x` — adding back what was subtracted.
/// The one-line bridge [`declare_euler_line`] needs to see `H' + 2O ~
/// A+B+C` straight from `H'`'s own definition, with no permutation toolkit
/// required.
fn add_sub_cancel_back(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    let creal = p.creal;
    let ny = cneg(d, p, y);
    let x_ny = cadd(d, p, x, ny);
    let lhs = cadd(d, p, x_ny, y);
    let ny_y = cadd(d, p, ny, y);
    let x_nyy = cadd(d, p, x, ny_y);
    let assoc = d.lemma(creal.add_assoc, &[x, ny, y]); // Equiv(lhs, x_nyy)
    let cancel = neg_add_cancel_proof(d, p, y); // Equiv(ny_y, zero)
    let zero = czero(d, p);
    let refl_x = refl(d, p, x);
    let congr = d.lemma(creal.add_congr, &[x, x, ny_y, zero, refl_x, cancel]); // Equiv(x_nyy, x_zero)
    let x_zero = cadd(d, p, x, zero);
    let az = d.lemma(creal.add_zero, &[x]); // Equiv(x_zero, x)
    chain(d, p, lhs, &[(x_nyy, assoc), (x_zero, congr), (x, az)])
}

/// Given the raw x- (or y-) coordinates `t1, t2, t3` of `A, B, C` (fixed
/// order) and `o`, the shared coordinate of `O`, together with `drop` (one
/// of `t1, t2, t3`, the vertex subtracted) and `kj, kk` (the other two, in
/// the desired output order), proves and returns `(lhs, rhs, proof)` where
///
/// `lhs = add (add (add (add t1 t2) t3) (neg (add o o))) (neg drop)`
/// `rhs = add (add kj (neg o)) (add kk (neg o))`
/// `proof : Equiv lhs rhs`
///
/// i.e. `(A+B+C-2O) - drop ~ (kj-O)+(kk-O)` — the coordinate content behind
/// [`declare_circumcentre_orthocentre_construction`]'s two altitude
/// telescopes (`H'-A ~ (B-O)+(C-O)` and `H'-B ~ (A-O)+(C-O)`). Built with the
/// same `SumTree`/[`reorder_right_chain`]/[`reduce3`] toolkit
/// [`declare_circumcentre_identity`] uses, rather than a bespoke chain: split
/// `neg (add o o)` into two leaves, flatten the resulting 6-leaf sum, reorder
/// so `drop` sits next to its own negation, and cancel.
fn h_prime_minus_vertex_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    t1: ExprId,
    t2: ExprId,
    t3: ExprId,
    o: ExprId,
    drop: ExprId,
    kj: ExprId,
    kk: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let creal = p.creal;
    let neg_drop = cneg(d, p, drop);
    let neg_o = cneg(d, p, o);
    let o_o = cadd(d, p, o, o);
    let neg_oo = cneg(d, p, o_o);
    let t1_t2 = cadd(d, p, t1, t2);
    let s3 = cadd(d, p, t1_t2, t3);
    let s3_negoo = cadd(d, p, s3, neg_oo);
    let lhs_raw = cadd(d, p, s3_negoo, neg_drop);

    // Split `neg (add o o)` into `add (neg o) (neg o)`.
    let split1 = neg_add_proof(d, p, o, o); // Equiv(neg_oo, add neg_o neg_o)
    let neg_o_neg_o = cadd(d, p, neg_o, neg_o);
    let refl_s3 = refl(d, p, s3);
    let step_mid = d.lemma(
        creal.add_congr,
        &[s3, s3, neg_oo, neg_o_neg_o, refl_s3, split1],
    ); // Equiv(s3_negoo, mid)
    let mid = cadd(d, p, s3, neg_o_neg_o);
    let refl_negdrop = refl(d, p, neg_drop);
    let step2 = d.lemma(
        creal.add_congr,
        &[s3_negoo, mid, neg_drop, neg_drop, step_mid, refl_negdrop],
    ); // Equiv(lhs_raw, target_full)

    // Build `target_full` as a pure sum-of-leaves tree.
    let tree = sadd(
        sadd(
            sadd(
                sadd(SumTree::Leaf(t1), SumTree::Leaf(t2)),
                SumTree::Leaf(t3),
            ),
            sadd(SumTree::Leaf(neg_o), SumTree::Leaf(neg_o)),
        ),
        SumTree::Leaf(neg_drop),
    );
    let target_full = sum_tree_build(d, p, &tree);
    let (chain_from, flatten_proof) = flatten_sum_tree(d, p, &tree); // Equiv(target_full, chain_from)

    let mut from_leaves = Vec::new();
    sum_tree_leaves(&tree, &mut from_leaves); // [t1, t2, t3, neg_o, neg_o, neg_drop]
    let to_leaves = vec![drop, neg_drop, kj, neg_o, kk, neg_o];
    let reorder_proof = reorder_right_chain(d, p, &from_leaves, &to_leaves);
    let chain_to = build_right_chain(d, p, &to_leaves);

    let remainder = build_right_chain(d, p, &[kj, neg_o, kk, neg_o]);
    let refl_drop = refl(d, p, drop);
    let reduce3_proof = reduce3(d, p, drop, drop, remainder, refl_drop); // Equiv(chain_to, remainder)

    let rhs_tree = sadd(
        sadd(SumTree::Leaf(kj), SumTree::Leaf(neg_o)),
        sadd(SumTree::Leaf(kk), SumTree::Leaf(neg_o)),
    );
    let rhs_raw = sum_tree_build(d, p, &rhs_tree);
    let (rhs_chain, rhs_flatten_proof) = flatten_sum_tree(d, p, &rhs_tree); // Equiv(rhs_raw, rhs_chain == remainder)
    let rhs_flatten_symm = symm(d, p, rhs_raw, rhs_chain, rhs_flatten_proof); // Equiv(remainder, rhs_raw)

    let proof = chain(
        d,
        p,
        lhs_raw,
        &[
            (target_full, step2),
            (chain_from, flatten_proof),
            (chain_to, reorder_proof),
            (remainder, reduce3_proof),
            (rhs_raw, rhs_flatten_symm),
        ],
    );
    (lhs_raw, rhs_raw, proof)
}

/// `Equiv (distSq O V) (dot (sub V O) (sub V O))` — bridges a hypothesis
/// stated over `distSq O _` (the natural way to say "equidistant from `O`")
/// to the raw `dot (vertex - O) (vertex - O)` form
/// [`declare_circumcentre_orthocentre_construction`]'s algebra is built in,
/// via `sub O V ~ neg (sub V O)` ([`point_sub_eq_neg_sub_fact`]) and
/// [`dot_neg_neg_proof`].
fn dist_sq_o_bridge(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    po: ExprId,
    ox: ExprId,
    oy: ExprId,
    pv: ExprId,
    vx: ExprId,
    vy: ExprId,
) -> ExprId {
    let sub_ov = psub(d, p, po, pv);
    let sub_vo = psub(d, p, pv, po);
    let neg_sub_vo = pneg(d, p, sub_vo);
    let fact = point_sub_eq_neg_sub_fact(d, p, vx, vy, ox, oy); // Equiv(sub_ov, neg_sub_vo)
    let congr = d.lemma(
        p.dot_congr,
        &[sub_ov, neg_sub_vo, sub_ov, neg_sub_vo, fact, fact],
    );
    let dot_negnegvo = dotp(d, p, neg_sub_vo, neg_sub_vo);
    let dnn = dot_neg_neg_proof(d, p, sub_vo); // Equiv(dot_negnegvo, dot(sub_vo, sub_vo))
    let dot_vovo = dotp(d, p, sub_vo, sub_vo);
    let dsq_ov = d.const_app(p.dist_sq, &[po, pv]);
    chain(d, p, dsq_ov, &[(dot_negnegvo, congr), (dot_vovo, dnn)])
}

/// **The heart of the Euler line.** See
/// [`CPointPrelude::circumcentre_orthocentre_construction`].
fn declare_circumcentre_orthocentre_construction(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
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
    let ox = d.const_app(p.x, &[po]);
    let oy = d.const_app(p.y, &[po]);

    let dsq_oa = d.const_app(p.dist_sq, &[po, pa]);
    let dsq_ob = d.const_app(p.dist_sq, &[po, pb]);
    let dsq_oc = d.const_app(p.dist_sq, &[po, pc]);

    let h1_ty = equiv(d, p, dsq_oa, dsq_ob);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = equiv(d, p, dsq_ob, dsq_oc);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let sum_ab = padd(d, p, pa, pb);
    let sum_abc = padd(d, p, sum_ab, pc);
    let two_o = padd(d, p, po, po);
    let h_prime = psub(d, p, sum_abc, two_o);

    // === Goal 1: dot (sub H' A) (sub C B) ~ zero. ===
    let big_x1 = psub(d, p, pb, po); // B - O
    let big_y1 = psub(d, p, pc, po); // C - O
    let big_w1 = padd(d, p, big_x1, big_y1); // ~ H' - A
    let big_z1 = psub(d, p, big_y1, big_x1); // ~ C - B

    let (lhs_x1, rhs_x1, proof_x1) =
        h_prime_minus_vertex_scalar_proof(d, p, ax, bx, cx, ox, ax, bx, cx);
    let (lhs_y1, rhs_y1, proof_y1) =
        h_prime_minus_vertex_scalar_proof(d, p, ay, by, cy, oy, ay, by, cy);
    let claim_x1 = equiv(d, p, lhs_x1, rhs_x1);
    let claim_y1 = equiv(d, p, lhs_y1, rhs_y1);
    let fact_ha = and_intro(d, p, claim_x1, claim_y1, proof_x1, proof_y1); // CPoint.Equiv (sub h_prime A) big_w1

    let fact_cb = point_diff_diff_fact(d, p, cx, cy, bx, by, ox, oy); // CPoint.Equiv (sub C B) big_z1

    let hprime_minus_a = psub(d, p, h_prime, pa);
    let sub_cb = psub(d, p, pc, pb);
    let congr1 = d.lemma(
        p.dot_congr,
        &[hprime_minus_a, big_w1, sub_cb, big_z1, fact_ha, fact_cb],
    ); // Equiv(dot(H'-A, C-B), dot(W1, Z1))

    let dal1 = d.lemma(p.dot_add_left, &[big_x1, big_y1, big_z1]);
    // Equiv(dot(W1,Z1), add(dot(X1,Z1))(dot(Y1,Z1)))
    let dsr_x1 = d.lemma(p.dot_sub_right, &[big_x1, big_y1, big_x1]);
    // Equiv(dot(X1,Z1), add(dot(X1,Y1))(neg(dot(X1,X1))))
    let t2_1 = dotp(d, p, big_x1, big_y1);
    let dot_x1x1_early = dotp(d, p, big_x1, big_x1);
    let t1_1 = cneg(d, p, dot_x1x1_early);
    let t2_1_t1_1 = cadd(d, p, t2_1, t1_1);

    let dsr_y1 = d.lemma(p.dot_sub_right, &[big_y1, big_y1, big_x1]);
    // Equiv(dot(Y1,Z1), add(dot(Y1,Y1))(neg(dot(Y1,X1))))
    let t4_1 = dotp(d, p, big_y1, big_y1);
    let raw_yx1 = dotp(d, p, big_y1, big_x1);
    let neg_raw_yx1 = cneg(d, p, raw_yx1);
    let comm_yx1 = d.lemma(p.dot_comm, &[big_y1, big_x1]); // Equiv(raw_yx1, t2_1)
    let neg_congr_yx1 = d.lemma(p.creal.neg_congr, &[raw_yx1, t2_1, comm_yx1]); // Equiv(neg_raw_yx1, t3_1)
    let t3_1 = cneg(d, p, t2_1);
    let refl_t4_1 = refl(d, p, t4_1);
    let congr_dsry1 = d.lemma(
        p.creal.add_congr,
        &[t4_1, t4_1, neg_raw_yx1, t3_1, refl_t4_1, neg_congr_yx1],
    ); // Equiv(add(t4_1,neg_raw_yx1), add(t4_1,t3_1))
    let t4_1_t3_1 = cadd(d, p, t4_1, t3_1);
    let dot_y1z1 = dotp(d, p, big_y1, big_z1);
    let t4_1_negrawyx1 = cadd(d, p, t4_1, neg_raw_yx1);
    let dot_y1z1_reduced = chain(
        d,
        p,
        dot_y1z1,
        &[(t4_1_negrawyx1, dsr_y1), (t4_1_t3_1, congr_dsry1)],
    ); // Equiv(dot(Y1,Z1), t4_1_t3_1)

    let dot_x1z1 = dotp(d, p, big_x1, big_z1);
    let congr_combine1 = d.lemma(
        p.creal.add_congr,
        &[
            dot_x1z1,
            t2_1_t1_1,
            dot_y1z1,
            t4_1_t3_1,
            dsr_x1,
            dot_y1z1_reduced,
        ],
    );
    let tree1_target = cadd(d, p, t2_1_t1_1, t4_1_t3_1);
    let dot_w1z1 = dotp(d, p, big_w1, big_z1);
    let dot_x1z1_y1z1 = cadd(d, p, dot_x1z1, dot_y1z1);
    let full_expand1 = chain(
        d,
        p,
        dot_w1z1,
        &[(dot_x1z1_y1z1, dal1), (tree1_target, congr_combine1)],
    ); // Equiv(dot(W1,Z1), (t2_1+t1_1)+(t4_1+t3_1))

    let tree1 = sadd(
        sadd(SumTree::Leaf(t2_1), SumTree::Leaf(t1_1)),
        sadd(SumTree::Leaf(t4_1), SumTree::Leaf(t3_1)),
    );
    let (chain_from1, flatten_proof1) = flatten_sum_tree(d, p, &tree1); // Equiv(tree1_target, chain_from1)
    let mut from_leaves1 = Vec::new();
    sum_tree_leaves(&tree1, &mut from_leaves1);
    let to_leaves1 = vec![t2_1, t3_1, t1_1, t4_1];
    let reorder_proof1 = reorder_right_chain(d, p, &from_leaves1, &to_leaves1);
    let chain_to1 = build_right_chain(d, p, &to_leaves1);
    let z1 = cadd(d, p, t1_1, t4_1);
    let refl_t2_1 = refl(d, p, t2_1);
    let reduce3_proof1 = reduce3(d, p, t2_1, t2_1, z1, refl_t2_1); // Equiv(chain_to1, z1)

    let bridge_b = dist_sq_o_bridge(d, p, po, ox, oy, pb, bx, by); // Equiv(dsq_ob, dot(X1,X1))
    let bridge_c = dist_sq_o_bridge(d, p, po, ox, oy, pc, cx, cy); // Equiv(dsq_oc, dot(Y1,Y1))
    let dot_x1x1 = dotp(d, p, big_x1, big_x1);
    let dot_y1y1 = dotp(d, p, big_y1, big_y1);
    let bridge_b_symm = symm(d, p, dsq_ob, dot_x1x1, bridge_b); // Equiv(dot(X1,X1), dsq_ob)
    let hxy1 = chain(
        d,
        p,
        dot_x1x1,
        &[(dsq_ob, bridge_b_symm), (dsq_oc, h2), (dot_y1y1, bridge_c)],
    ); // Equiv(dot(X1,X1), dot(Y1,Y1))
    let final_cancel1 = cancel_neg_pos(d, p, dot_x1x1, dot_y1y1, hxy1); // Equiv(z1, zero)
    let zero = czero(d, p);

    let dot_hprimea_cb = dotp(d, p, hprime_minus_a, sub_cb);
    let goal1_proof = chain(
        d,
        p,
        dot_hprimea_cb,
        &[
            (dot_w1z1, congr1),
            (tree1_target, full_expand1),
            (chain_from1, flatten_proof1),
            (chain_to1, reorder_proof1),
            (z1, reduce3_proof1),
            (zero, final_cancel1),
        ],
    );

    // === Goal 2: dot (sub H' B) (sub A C) ~ zero. ===
    let big_x2 = psub(d, p, pa, po); // A - O
    let big_y2 = big_y1; // C - O  (shared with goal 1)
    let big_w2 = padd(d, p, big_x2, big_y2); // ~ H' - B
    let big_z2 = psub(d, p, big_x2, big_y2); // ~ A - C

    let (lhs_x2, rhs_x2, proof_x2) =
        h_prime_minus_vertex_scalar_proof(d, p, ax, bx, cx, ox, bx, ax, cx);
    let (lhs_y2, rhs_y2, proof_y2) =
        h_prime_minus_vertex_scalar_proof(d, p, ay, by, cy, oy, by, ay, cy);
    let claim_x2 = equiv(d, p, lhs_x2, rhs_x2);
    let claim_y2 = equiv(d, p, lhs_y2, rhs_y2);
    let fact_hb = and_intro(d, p, claim_x2, claim_y2, proof_x2, proof_y2); // CPoint.Equiv (sub h_prime B) big_w2

    let fact_ac = point_diff_diff_fact(d, p, ax, ay, cx, cy, ox, oy); // CPoint.Equiv (sub A C) big_z2

    let hprime_minus_b = psub(d, p, h_prime, pb);
    let sub_ac = psub(d, p, pa, pc);
    let congr2 = d.lemma(
        p.dot_congr,
        &[hprime_minus_b, big_w2, sub_ac, big_z2, fact_hb, fact_ac],
    ); // Equiv(dot(H'-B, A-C), dot(W2, Z2))

    let dal2 = d.lemma(p.dot_add_left, &[big_x2, big_y2, big_z2]);
    let dsr_x2 = d.lemma(p.dot_sub_right, &[big_x2, big_x2, big_y2]);
    // Equiv(dot(X2,Z2), add(dot(X2,X2))(neg(dot(X2,Y2))))
    let a1_2 = dotp(d, p, big_x2, big_x2);
    let t2_2 = dotp(d, p, big_x2, big_y2);
    let a3_2 = cneg(d, p, t2_2);
    let a1_2_a3_2 = cadd(d, p, a1_2, a3_2);

    let dsr_y2 = d.lemma(p.dot_sub_right, &[big_y2, big_x2, big_y2]);
    // Equiv(dot(Y2,Z2), add(dot(Y2,X2))(neg(dot(Y2,Y2))))
    let raw_yx2 = dotp(d, p, big_y2, big_x2);
    let a4_2 = dotp(d, p, big_y2, big_y2);
    let neg_a4_2 = cneg(d, p, a4_2);
    let comm_yx2 = d.lemma(p.dot_comm, &[big_y2, big_x2]); // Equiv(raw_yx2, t2_2)
    let refl_neg_a4_2 = refl(d, p, neg_a4_2);
    let congr_dsry2 = d.lemma(
        p.creal.add_congr,
        &[raw_yx2, t2_2, neg_a4_2, neg_a4_2, comm_yx2, refl_neg_a4_2],
    ); // Equiv(add(raw_yx2,neg_a4_2), add(t2_2,neg_a4_2))
    let t2_2_neg_a4_2 = cadd(d, p, t2_2, neg_a4_2);
    let dot_y2z2 = dotp(d, p, big_y2, big_z2);
    let raw_yx2_neg_a4_2 = cadd(d, p, raw_yx2, neg_a4_2);
    let dot_y2z2_reduced = chain(
        d,
        p,
        dot_y2z2,
        &[(raw_yx2_neg_a4_2, dsr_y2), (t2_2_neg_a4_2, congr_dsry2)],
    ); // Equiv(dot(Y2,Z2), t2_2_neg_a4_2)

    let dot_x2z2 = dotp(d, p, big_x2, big_z2);
    let congr_combine2 = d.lemma(
        p.creal.add_congr,
        &[
            dot_x2z2,
            a1_2_a3_2,
            dot_y2z2,
            t2_2_neg_a4_2,
            dsr_x2,
            dot_y2z2_reduced,
        ],
    );
    let tree2_target = cadd(d, p, a1_2_a3_2, t2_2_neg_a4_2);
    let dot_w2z2 = dotp(d, p, big_w2, big_z2);
    let dot_x2z2_y2z2 = cadd(d, p, dot_x2z2, dot_y2z2);
    let full_expand2 = chain(
        d,
        p,
        dot_w2z2,
        &[(dot_x2z2_y2z2, dal2), (tree2_target, congr_combine2)],
    );

    let tree2 = sadd(
        sadd(SumTree::Leaf(a1_2), SumTree::Leaf(a3_2)),
        sadd(SumTree::Leaf(t2_2), SumTree::Leaf(neg_a4_2)),
    );
    let (chain_from2, flatten_proof2) = flatten_sum_tree(d, p, &tree2);
    let mut from_leaves2 = Vec::new();
    sum_tree_leaves(&tree2, &mut from_leaves2);
    let to_leaves2 = vec![t2_2, a3_2, a1_2, neg_a4_2];
    let reorder_proof2 = reorder_right_chain(d, p, &from_leaves2, &to_leaves2);
    let chain_to2 = build_right_chain(d, p, &to_leaves2);
    let z2 = cadd(d, p, a1_2, neg_a4_2);
    let refl_t2_2 = refl(d, p, t2_2);
    let reduce3_proof2 = reduce3(d, p, t2_2, t2_2, z2, refl_t2_2);

    let h13 = d.lemma(p.circumcentre_third_distance, &[po, pa, pb, pc, h1, h2]); // Equiv(dsq_oa, dsq_oc)
    let bridge_a = dist_sq_o_bridge(d, p, po, ox, oy, pa, ax, ay); // Equiv(dsq_oa, dot(X2,X2))
    let bridge_a_symm = symm(d, p, dsq_oa, a1_2, bridge_a); // Equiv(dot(X2,X2), dsq_oa)
    let hxy2 = chain(
        d,
        p,
        a1_2,
        &[(dsq_oa, bridge_a_symm), (dsq_oc, h13), (a4_2, bridge_c)],
    ); // Equiv(dot(X2,X2), dot(Y2,Y2))  [bridge_c reused from goal 1: Y2 == Y1]
    let final_cancel2 = cancel_pos_neg(d, p, a1_2, a4_2, hxy2); // Equiv(z2, zero)

    let dot_hprimeb_ac = dotp(d, p, hprime_minus_b, sub_ac);
    let goal2_proof = chain(
        d,
        p,
        dot_hprimeb_ac,
        &[
            (dot_w2z2, congr2),
            (tree2_target, full_expand2),
            (chain_from2, flatten_proof2),
            (chain_to2, reorder_proof2),
            (z2, reduce3_proof2),
            (zero, final_cancel2),
        ],
    );

    let concl1_ty = equiv(d, p, dot_hprimea_cb, zero);
    let concl2_ty = equiv(d, p, dot_hprimeb_ac, zero);
    let conclusion = and_intro(d, p, concl1_ty, concl2_ty, goal1_proof, goal2_proof);

    let ty_body = {
        let and_ty = p.creal.rat.int.logic.and;
        let and_concl = d.const_app(and_ty, &[concl1_ty, concl2_ty]);
        let inner = d.arrow(h2_ty, and_concl);
        d.arrow(h1_ty, inner)
    };
    let ty = {
        let w4 = d.pi_fv(c_fv, point, ty_body);
        let w3 = d.pi_fv(b_fv, point, w4);
        let w2 = d.pi_fv(a_fv, point, w3);
        d.pi_fv(o_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h2_fv, h2_ty, conclusion);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, inner);
        let w4 = d.lam_fv(c_fv, point, with_h1);
        let w3 = d.lam_fv(b_fv, point, w4);
        let w2 = d.lam_fv(a_fv, point, w3);
        d.lam_fv(o_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.circumcentre_orthocentre_construction,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The Euler line, additive form.** See [`CPointPrelude::euler_line`].
fn declare_euler_line(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
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

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);
    let ox = d.const_app(p.x, &[po]);
    let oy = d.const_app(p.y, &[po]);

    let sum_ab = padd(d, p, pa, pb);
    let sum_abc = padd(d, p, sum_ab, pc);
    let two_o = padd(d, p, po, po);
    let h_prime = psub(d, p, sum_abc, two_o);
    let h_prime_plus_two_o = padd(d, p, h_prime, two_o);

    let big_g = d.const_app(p.centroid, &[pa, pb, pc]);
    let gg = padd(d, p, big_g, big_g);
    let ggg = padd(d, p, gg, big_g);

    let three = d.kernel().const_(p.three, vec![]);

    let build_coord = |d: &mut IntDev<'_>, t1: ExprId, t2: ExprId, t3: ExprId, o: ExprId| {
        let t1_t2 = cadd(d, p, t1, t2);
        let s3 = cadd(d, p, t1_t2, t3);
        let oo = cadd(d, p, o, o);
        let neg_oo = cneg(d, p, oo);
        let hprime_coord = cadd(d, p, s3, neg_oo);
        let lhs = cadd(d, p, hprime_coord, oo); // x/y (H' + 2O)

        let cancel_back = add_sub_cancel_back(d, p, s3, oo); // Equiv(lhs, s3)

        let assoc_s3 = d.lemma(creal.add_assoc, &[t1, t2, t3]); // Equiv(s3, t1+(t2+t3))
        let t23 = cadd(d, p, t2, t3);
        let t1_t23 = cadd(d, p, t1, t23);

        let gx = ccentroid_raw(d, p, t1, t2, t3);
        let mul_three_gx = cmul(d, p, three, gx);
        let tgs = triple_g_eq_sum_proof(d, p, t1, t2, t3); // Equiv(mul_three_gx, t1_t23)
        let tgs_symm = symm(d, p, mul_three_gx, t1_t23, tgs); // Equiv(t1_t23, mul_three_gx)

        let gxgx = cadd(d, p, gx, gx);
        let gxgx_gx = cadd(d, p, gxgx, gx);
        let tmet = three_mul_eq_triple_proof(d, p, gx); // Equiv(mul_three_gx, gxgx_gx)

        let proof = chain(
            d,
            p,
            lhs,
            &[
                (s3, cancel_back),
                (t1_t23, assoc_s3),
                (mul_three_gx, tgs_symm),
                (gxgx_gx, tmet),
            ],
        );
        (lhs, gxgx_gx, proof)
    };

    let (lhs_x, rhs_x, proof_x) = build_coord(d, ax, bx, cx, ox);
    let (lhs_y, rhs_y, proof_y) = build_coord(d, ay, by, cy, oy);

    let claim_x = equiv(d, p, lhs_x, rhs_x);
    let claim_y = equiv(d, p, lhs_y, rhs_y);
    let proof = and_intro(d, p, claim_x, claim_y, proof_x, proof_y);

    let ty_body = d.const_app(p.point_equiv, &[h_prime_plus_two_o, ggg]);
    let ty = {
        let w3 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w3);
        let w1 = d.pi_fv(a_fv, point, w2);
        d.pi_fv(o_fv, point, w1)
    };
    let value = {
        let w3 = d.lam_fv(c_fv, point, proof);
        let w2 = d.lam_fv(b_fv, point, w3);
        let w1 = d.lam_fv(a_fv, point, w2);
        d.lam_fv(o_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.euler_line,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the bridge: `apollonius_median` from `stewart_median` -----------------

/// `Equiv (add b (neg (mul inv2 (add b c)))) (mul inv2 (add b (neg c)))` —
/// `b - midpoint(b,c) ~ inv2·(b-c)` at the raw-scalar level (`midpoint`
/// written in its already-unfolded `mul inv2 (add _ _)` form, matching
/// [`double_midpoint_proof`]'s convention). The per-coordinate content of
/// [`CPointPrelude::midpoint_dist_sq_quarter`]: `b` is telescoped via
/// [`half_double_proof`] into `ib+ib` (`ib := mul inv2 b`), the midpoint's
/// own `left_distrib` unfolding turns the subtracted term into `ib+ic`, and
/// an `add_middle_swap_proof` cancels the shared `ib`, leaving `ib - ic =
/// inv2·(b-c)` ([`mul_sub_right_proof`], reversed).
fn sub_midpoint_scalar_proof(d: &mut IntDev<'_>, p: CPointPrelude, b: ExprId, c: ExprId) -> ExprId {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let bc = cadd(d, p, b, c);
    let m = cmul(d, p, inv2, bc);
    let neg_m = cneg(d, p, m);
    let lhs = cadd(d, p, b, neg_m);

    let ib = cmul(d, p, inv2, b);
    let ic = cmul(d, p, inv2, c);

    let hd = half_double_proof(d, p, b); // Equiv(b, ib+ib)
    let ib_ib = cadd(d, p, ib, ib);
    let refl_negm = refl(d, p, neg_m);
    let congr1 = d.lemma(creal.add_congr, &[b, ib_ib, neg_m, neg_m, hd, refl_negm]);
    let ib_ib_negm = cadd(d, p, ib_ib, neg_m);

    let ib_ic = cadd(d, p, ib, ic);
    let ld = d.lemma(creal.left_distrib, &[inv2, b, c]); // Equiv(m, ib_ic)
    let neg_congr = d.lemma(creal.neg_congr, &[m, ib_ic, ld]); // Equiv(neg_m, neg(ib_ic))
    let neg_ib_ic = cneg(d, p, ib_ic);
    let refl_ibib_a = refl(d, p, ib_ib);
    let congr2 = d.lemma(
        creal.add_congr,
        &[ib_ib, ib_ib, neg_m, neg_ib_ic, refl_ibib_a, neg_congr],
    );
    let ib_ib_negibic = cadd(d, p, ib_ib, neg_ib_ic);

    let nap = neg_add_proof(d, p, ib, ic); // Equiv(neg_ib_ic, add(neg ib)(neg ic))
    let neg_ib = cneg(d, p, ib);
    let neg_ic = cneg(d, p, ic);
    let negib_negic = cadd(d, p, neg_ib, neg_ic);
    let refl_ibib_b = refl(d, p, ib_ib);
    let congr3 = d.lemma(
        creal.add_congr,
        &[ib_ib, ib_ib, neg_ib_ic, negib_negic, refl_ibib_b, nap],
    );
    let ib_ib_negibnegic = cadd(d, p, ib_ib, negib_negic);

    let swap = add_middle_swap_proof(d, p, ib, ib, neg_ib, neg_ic);
    // Equiv((ib+ib)+(neg_ib+neg_ic), (ib+neg_ib)+(ib+neg_ic))
    let ib_negib = cadd(d, p, ib, neg_ib);
    let ib_negic = cadd(d, p, ib, neg_ic);
    let swapped = cadd(d, p, ib_negib, ib_negic);

    let an = d.lemma(creal.add_neg, &[ib]); // Equiv(ib_negib, zero)
    let zero = czero(d, p);
    let refl_ibnegic = refl(d, p, ib_negic);
    let congr4 = d.lemma(
        creal.add_congr,
        &[ib_negib, zero, ib_negic, ib_negic, an, refl_ibnegic],
    );
    let zero_ibnegic = cadd(d, p, zero, ib_negic);
    let za = zero_add_proof(d, p, ib_negic); // Equiv(zero_ibnegic, ib_negic)

    let neg_c = cneg(d, p, c);
    let b_negc = cadd(d, p, b, neg_c);
    let target = cmul(d, p, inv2, b_negc);
    let msr = mul_sub_right_proof(d, p, inv2, b, c); // Equiv(target, ib_negic)
    let msr_symm = symm(d, p, target, ib_negic, msr); // Equiv(ib_negic, target)

    chain(
        d,
        p,
        lhs,
        &[
            (ib_ib_negm, congr1),
            (ib_ib_negibic, congr2),
            (ib_ib_negibnegic, congr3),
            (swapped, swap),
            (zero_ibnegic, congr4),
            (ib_negic, za),
            (target, msr_symm),
        ],
    )
}

/// **`BM² = ¼BC²`.** See [`CPointPrelude::midpoint_dist_sq_quarter`].
fn declare_midpoint_dist_sq_quarter(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
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

    let inv2 = d.kernel().const_(p.inv2, vec![]);

    let build_coord = |d: &mut IntDev<'_>, bv: ExprId, cv: ExprId| {
        let sv = sub_midpoint_scalar_proof(d, p, bv, cv); // Equiv(bv - mv, inv2*(bv-cv))
        let bc = cadd(d, p, bv, cv);
        let mv = cmul(d, p, inv2, bc);
        let neg_mv = cneg(d, p, mv);
        let bmv = cadd(d, p, bv, neg_mv);

        let neg_cv = cneg(d, p, cv);
        let bv_cv = cadd(d, p, bv, neg_cv);
        let inv2_bvcv = cmul(d, p, inv2, bv_cv);

        let dist_raw = cmul(d, p, bmv, bmv);
        let sq_congr = d.lemma(creal.mul_congr, &[bmv, inv2_bvcv, bmv, inv2_bvcv, sv, sv]);
        let sq_raw = cmul(d, p, inv2_bvcv, inv2_bvcv);
        let sqscale = sq_scale_proof(d, p, inv2, bv_cv); // Equiv(sq_raw, mul inv2 (mul inv2 (mul bv_cv bv_cv)))
        let vsq = cmul(d, p, bv_cv, bv_cv);
        let inv2_vsq = cmul(d, p, inv2, vsq);
        let target = cmul(d, p, inv2, inv2_vsq);
        let dist_total = chain(d, p, dist_raw, &[(sq_raw, sq_congr), (target, sqscale)]);
        (dist_raw, vsq, inv2_vsq, target, dist_total)
    };

    let (dist_x_raw, xsq, inv2_xsq, target_x, dist_x_total) = build_coord(d, bx, cx);
    let (dist_y_raw, ysq, inv2_ysq, target_y, dist_y_total) = build_coord(d, by, cy);

    let distsq_bm_raw = cadd(d, p, dist_x_raw, dist_y_raw);
    let combined = cadd(d, p, target_x, target_y);
    let sum_congr = d.lemma(
        creal.add_congr,
        &[
            dist_x_raw,
            target_x,
            dist_y_raw,
            target_y,
            dist_x_total,
            dist_y_total,
        ],
    );

    let xsq_ysq = cadd(d, p, xsq, ysq);
    let d1 = d.lemma(creal.left_distrib, &[inv2, xsq, ysq]); // Equiv(inv2*(xsq+ysq), inv2*xsq+inv2*ysq)
    let inv2_xsqysq = cmul(d, p, inv2, xsq_ysq);
    let inv2_xsq_inv2_ysq = cadd(d, p, inv2_xsq, inv2_ysq);
    let refl_inv2 = refl(d, p, inv2);
    let d2congr = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, inv2_xsqysq, inv2_xsq_inv2_ysq, refl_inv2, d1],
    );
    let target_full = cmul(d, p, inv2, inv2_xsqysq);
    let mul_inv2_sum = cmul(d, p, inv2, inv2_xsq_inv2_ysq);
    let d2 = d.lemma(creal.left_distrib, &[inv2, inv2_xsq, inv2_ysq]); // Equiv(mul_inv2_sum, target_x+target_y == combined)
    let full_reverse = chain(
        d,
        p,
        target_full,
        &[(mul_inv2_sum, d2congr), (combined, d2)],
    );
    let final_reverse = symm(d, p, target_full, combined, full_reverse); // Equiv(combined, target_full)

    let final_proof = chain(
        d,
        p,
        distsq_bm_raw,
        &[(combined, sum_congr), (target_full, final_reverse)],
    );

    let big_m = d.const_app(p.point_midpoint, &[pb, pc]);
    let dsq_bm = d.const_app(p.dist_sq, &[pb, big_m]);
    let dsq_bc = d.const_app(p.dist_sq, &[pb, pc]);
    let inv2_dsq_bc = cmul(d, p, inv2, dsq_bc);
    let rhs_nice = cmul(d, p, inv2, inv2_dsq_bc);
    let ty_body = equiv(d, p, dsq_bm, rhs_nice);
    let ty = {
        let w1 = d.pi_fv(c_fv, point, ty_body);
        d.pi_fv(b_fv, point, w1)
    };
    let value = {
        let w1 = d.lam_fv(c_fv, point, final_proof);
        d.lam_fv(b_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.midpoint_dist_sq_quarter,
        uparams: vec![],
        ty,
        value,
    })
}

/// **`apollonius_median`, re-derived from `stewart_median`.** See
/// [`CPointPrelude::apollonius_from_stewart`].
fn declare_apollonius_from_stewart(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let inv2 = d.kernel().const_(p.inv2, vec![]);

    let stewart_inst = d.lemma(p.stewart_median, &[pa, pb, pc]); // Equiv(l, r)

    let big_m = d.const_app(p.point_midpoint, &[pb, pc]);
    let dsq_am = d.const_app(p.dist_sq, &[pa, big_m]);
    let dsq_bc = d.const_app(p.dist_sq, &[pb, pc]);
    let inv2_dsqbc = cmul(d, p, inv2, dsq_bc);
    let inv2_inv2_dsqbc = cmul(d, p, inv2, inv2_dsqbc);
    let l = cadd(d, p, dsq_am, inv2_inv2_dsqbc);

    let dsq_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dsq_ac = d.const_app(p.dist_sq, &[pa, pc]);
    let inv2_ab = cmul(d, p, inv2, dsq_ab);
    let inv2_ac = cmul(d, p, inv2, dsq_ac);
    let r = cadd(d, p, inv2_ab, inv2_ac);

    let ll = cadd(d, p, l, l);
    let rr = cadd(d, p, r, r);
    let doubled = d.lemma(creal.add_congr, &[l, r, l, r, stewart_inst, stewart_inst]); // Equiv(ll, rr)

    let swap_l = add_middle_swap_proof(d, p, dsq_am, inv2_inv2_dsqbc, dsq_am, inv2_inv2_dsqbc);
    let am_am = cadd(d, p, dsq_am, dsq_am);
    let sq_sq = cadd(d, p, inv2_inv2_dsqbc, inv2_inv2_dsqbc);
    let ll_regrouped = cadd(d, p, am_am, sq_sq);

    let dsq_bm = d.const_app(p.dist_sq, &[pb, big_m]);
    let mdq = d.lemma(p.midpoint_dist_sq_quarter, &[pb, pc]); // Equiv(dsq_bm, inv2_inv2_dsqbc)
    let mdq_symm = symm(d, p, dsq_bm, inv2_inv2_dsqbc, mdq); // Equiv(inv2_inv2_dsqbc, dsq_bm)
    let sq_sq_congr = d.lemma(
        creal.add_congr,
        &[
            inv2_inv2_dsqbc,
            dsq_bm,
            inv2_inv2_dsqbc,
            dsq_bm,
            mdq_symm,
            mdq_symm,
        ],
    );
    let bm_bm = cadd(d, p, dsq_bm, dsq_bm);
    let refl_amam = refl(d, p, am_am);
    let ll_final_congr = d.lemma(
        creal.add_congr,
        &[am_am, am_am, sq_sq, bm_bm, refl_amam, sq_sq_congr],
    );
    let am_am_bm_bm = cadd(d, p, am_am, bm_bm);
    let ll_to_amambmbm = chain(
        d,
        p,
        ll,
        &[(ll_regrouped, swap_l), (am_am_bm_bm, ll_final_congr)],
    );

    let swap_r = add_middle_swap_proof(d, p, inv2_ab, inv2_ac, inv2_ab, inv2_ac);
    let ab_ab2 = cadd(d, p, inv2_ab, inv2_ab);
    let ac_ac2 = cadd(d, p, inv2_ac, inv2_ac);
    let rr_regrouped = cadd(d, p, ab_ab2, ac_ac2);

    let hd_ab = half_double_proof(d, p, dsq_ab); // Equiv(dsq_ab, ab_ab2)
    let hd_ab_symm = symm(d, p, dsq_ab, ab_ab2, hd_ab); // Equiv(ab_ab2, dsq_ab)
    let hd_ac = half_double_proof(d, p, dsq_ac);
    let hd_ac_symm = symm(d, p, dsq_ac, ac_ac2, hd_ac);
    let rr_final_congr = d.lemma(
        creal.add_congr,
        &[ab_ab2, dsq_ab, ac_ac2, dsq_ac, hd_ab_symm, hd_ac_symm],
    );
    let ab_ac = cadd(d, p, dsq_ab, dsq_ac);
    let rr_to_abac = chain(d, p, rr, &[(rr_regrouped, swap_r), (ab_ac, rr_final_congr)]);

    let rr_to_abac_symm = symm(d, p, rr, ab_ac, rr_to_abac); // Equiv(ab_ac, rr)
    let doubled_symm = symm(d, p, ll, rr, doubled); // Equiv(rr, ll)

    let final_proof = chain(
        d,
        p,
        ab_ac,
        &[
            (rr, rr_to_abac_symm),
            (ll, doubled_symm),
            (am_am_bm_bm, ll_to_amambmbm),
        ],
    );

    let ty_body = equiv(d, p, ab_ac, am_am_bm_bm);
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
        name: p.apollonius_from_stewart,
        uparams: vec![],
        ty,
        value,
    })
}

// --- Cauchy-Schwarz and the triangle inequality -----------------------------
//
// The inner-product-space axioms `dot` was always missing: positive
// semidefiniteness ([`declare_dot_self_nonneg`]), the squared Cauchy-Schwarz
// inequality ([`declare_cauchy_schwarz`], via [`declare_lagrange_identity`]),
// and the factor-2 triangle inequality for `distSq`
// ([`declare_dist_sq_double_sum_bound`]). No square root is introduced
// anywhere below (at the time this was written the kernel had
// `CReal.natSqrt` but no `CReal.sqrt`; `CReal.sqrt` landed 2026-08-26, but
// this section was never rebuilt around it — see `metric.rs`'s
// `Metric.CPoint.dotLeSqrtMul`/`distTriangle` for the unsquared route built
// on top of these), so every statement below is either squared or carries
// an explicit factor of 2 in place of a division this development cannot
// perform on an arbitrary term.

/// `Equiv (mul (mul x y) (mul z w)) (mul (mul x z) (mul y w))` — swap the
/// middle two factors of a four-fold product. The multiplicative analogue of
/// [`add_middle_swap_proof`], and the one new *pattern* the Lagrange-identity
/// proof needs: every monomial-matching step there is an instance of it.
fn four_factor_swap_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    w: ExprId,
) -> ExprId {
    let creal = p.creal;
    let zw = cmul(d, p, z, w);
    let xy = cmul(d, p, x, y);
    let xy_zw = cmul(d, p, xy, zw);
    let y_zw = cmul(d, p, y, zw);
    let x_yzw = cmul(d, p, x, y_zw);
    let step1 = d.lemma(creal.mul_assoc, &[x, y, zw]); // Equiv(xy_zw, x_yzw)

    let yz = cmul(d, p, y, z);
    let yz_w = cmul(d, p, yz, w);
    let assoc_a = d.lemma(creal.mul_assoc, &[y, z, w]); // Equiv(yz_w, y_zw)
    let assoc_a_symm = symm(d, p, yz_w, y_zw, assoc_a); // Equiv(y_zw, yz_w)
    let zy = cmul(d, p, z, y);
    let comm_yz = d.lemma(creal.mul_comm, &[y, z]); // Equiv(yz, zy)
    let refl_w = refl(d, p, w);
    let congr_zy_w = d.lemma(creal.mul_congr, &[yz, zy, w, w, comm_yz, refl_w]); // Equiv(yz_w, zy_w)
    let zy_w = cmul(d, p, zy, w);
    let yw = cmul(d, p, y, w);
    let assoc_b = d.lemma(creal.mul_assoc, &[z, y, w]); // Equiv(zy_w, z_yw)
    let z_yw = cmul(d, p, z, yw);
    let y_to_z_yw = chain(
        d,
        p,
        y_zw,
        &[(yz_w, assoc_a_symm), (zy_w, congr_zy_w), (z_yw, assoc_b)],
    ); // Equiv(y_zw, z_yw)

    let refl_x = refl(d, p, x);
    let congr_x = d.lemma(creal.mul_congr, &[x, x, y_zw, z_yw, refl_x, y_to_z_yw]); // Equiv(x_yzw, x_zyw)
    let x_zyw = cmul(d, p, x, z_yw);

    let xz = cmul(d, p, x, z);
    let xz_yw = cmul(d, p, xz, yw);
    let assoc_c = d.lemma(creal.mul_assoc, &[x, z, yw]); // Equiv(xz_yw, x_zyw)
    let assoc_c_symm = symm(d, p, xz_yw, x_zyw, assoc_c); // Equiv(x_zyw, xz_yw)

    chain(
        d,
        p,
        xy_zw,
        &[(x_yzw, step1), (x_zyw, congr_x), (xz_yw, assoc_c_symm)],
    )
}

/// Expand `mul (add x1 x2) (add y1 y2)` into the right-associated 4-term
/// chain `x1*y1 + (x1*y2 + (x2*y1 + x2*y2))`. Returns `(original, chain,
/// proof : Equiv(original, chain))`.
fn expand_mul_sum2(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x1: ExprId,
    x2: ExprId,
    y1: ExprId,
    y2: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let creal = p.creal;
    let sum_x = cadd(d, p, x1, x2);
    let sum_y = cadd(d, p, y1, y2);
    let original = cmul(d, p, sum_x, sum_y);

    let step1 = right_distrib_proof(d, p, x1, x2, sum_y); // Equiv(original, add(x1*sy)(x2*sy))
    let x1_sy = cmul(d, p, x1, sum_y);
    let x2_sy = cmul(d, p, x2, sum_y);
    let mid = cadd(d, p, x1_sy, x2_sy);

    let x1y1 = cmul(d, p, x1, y1);
    let x1y2 = cmul(d, p, x1, y2);
    let x2y1 = cmul(d, p, x2, y1);
    let x2y2 = cmul(d, p, x2, y2);
    let ld1 = d.lemma(creal.left_distrib, &[x1, y1, y2]); // Equiv(x1_sy, add x1y1 x1y2)
    let ld2 = d.lemma(creal.left_distrib, &[x2, y1, y2]); // Equiv(x2_sy, add x2y1 x2y2)
    let left_pair = cadd(d, p, x1y1, x1y2);
    let right_pair = cadd(d, p, x2y1, x2y2);
    let congr = d.lemma(
        creal.add_congr,
        &[x1_sy, left_pair, x2_sy, right_pair, ld1, ld2],
    );
    let nested = cadd(d, p, left_pair, right_pair);

    let tree = sadd(
        sadd(SumTree::Leaf(x1y1), SumTree::Leaf(x1y2)),
        sadd(SumTree::Leaf(x2y1), SumTree::Leaf(x2y2)),
    );
    let (chain_result, flatten_proof) = flatten_sum_tree(d, p, &tree);
    let full = chain(
        d,
        p,
        original,
        &[(mid, step1), (nested, congr), (chain_result, flatten_proof)],
    );
    (original, chain_result, full)
}

/// Given `Equiv(li, mi)` for `i=0..3`, produce
/// `Equiv (build_right_chain [l0,l1,l2,l3]) (build_right_chain [m0,m1,m2,m3])`.
#[allow(clippy::too_many_arguments)]
fn rewrite_right_chain4(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    l0: ExprId,
    l1: ExprId,
    l2: ExprId,
    l3: ExprId,
    m0: ExprId,
    m1: ExprId,
    m2: ExprId,
    m3: ExprId,
    p0: ExprId,
    p1: ExprId,
    p2: ExprId,
    p3: ExprId,
) -> ExprId {
    let creal = p.creal;
    let l23 = cadd(d, p, l2, l3);
    let m23 = cadd(d, p, m2, m3);
    let c23 = d.lemma(creal.add_congr, &[l2, m2, l3, m3, p2, p3]); // Equiv(l23, m23)
    let l123 = cadd(d, p, l1, l23);
    let m123 = cadd(d, p, m1, m23);
    let c123 = d.lemma(creal.add_congr, &[l1, m1, l23, m23, p1, c23]); // Equiv(l123, m123)
    d.lemma(creal.add_congr, &[l0, m0, l123, m123, p0, c123])
}

/// `Equiv (neg (build_right_chain [x0,x1,x2,x3])) (build_right_chain [neg x0,
/// neg x1, neg x2, neg x3])`.
fn neg_distribute_chain4(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x0: ExprId,
    x1: ExprId,
    x2: ExprId,
    x3: ExprId,
) -> ExprId {
    let creal = p.creal;
    let x23 = cadd(d, p, x2, x3);
    let x123 = cadd(d, p, x1, x23);
    let chain0 = cadd(d, p, x0, x123);

    let n0 = cneg(d, p, x0);
    let n1 = cneg(d, p, x1);
    let n2 = cneg(d, p, x2);
    let n3 = cneg(d, p, x3);

    let step23 = neg_add_proof(d, p, x2, x3); // Equiv(neg x23, add n2 n3)
    let n23 = cneg(d, p, x23);
    let n2n3 = cadd(d, p, n2, n3);

    let step123_pre = neg_add_proof(d, p, x1, x23); // Equiv(neg x123, add n1 (neg x23))
    let neg_x123 = cneg(d, p, x123);
    let n1_n23 = cadd(d, p, n1, n23);
    let refl_n1 = refl(d, p, n1);
    let congr1 = d.lemma(creal.add_congr, &[n1, n1, n23, n2n3, refl_n1, step23]); // Equiv(n1_n23, n1_n2n3)
    let n1_n2n3 = cadd(d, p, n1, n2n3);
    let step123 = chain(d, p, neg_x123, &[(n1_n23, step123_pre), (n1_n2n3, congr1)]);
    // step123: Equiv(neg x123, n1_n2n3)

    let step0_pre = neg_add_proof(d, p, x0, x123); // Equiv(neg chain0, add n0 (neg x123))
    let neg_chain0 = cneg(d, p, chain0);
    let n0_negx123 = cadd(d, p, n0, neg_x123);
    let refl_n0 = refl(d, p, n0);
    let congr0 = d.lemma(
        creal.add_congr,
        &[n0, n0, neg_x123, n1_n2n3, refl_n0, step123],
    ); // Equiv(n0_negx123, n0_n1n2n3)
    let n0_n1n2n3 = cadd(d, p, n0, n1_n2n3);
    chain(
        d,
        p,
        neg_chain0,
        &[(n0_negx123, step0_pre), (n0_n1n2n3, congr0)],
    )
}

/// `Equiv (add x (add (neg x) (add y (add (neg y) rest)))) rest` — two
/// cancelling pairs at the front of a chain, absorbed into whatever `rest`
/// is (opaque, not necessarily flattened further).
fn cancel_two_pairs_prefix(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    rest: ExprId,
) -> ExprId {
    let creal = p.creal;
    let nx = cneg(d, p, x);
    let ny = cneg(d, p, y);
    let zero = czero(d, p);
    let refl_rest = refl(d, p, rest);

    let ny_rest = cadd(d, p, ny, rest);
    let y_nyrest = cadd(d, p, y, ny_rest);
    let y_ny = cadd(d, p, y, ny);
    let y_ny_rest = cadd(d, p, y_ny, rest);
    let assoc_y = d.lemma(creal.add_assoc, &[y, ny, rest]); // Equiv(y_ny_rest, y_nyrest)
    let assoc_y_symm = symm(d, p, y_ny_rest, y_nyrest, assoc_y); // Equiv(y_nyrest, y_ny_rest)
    let an_y = d.lemma(creal.add_neg, &[y]); // Equiv(y_ny, zero)
    let zero_rest = cadd(d, p, zero, rest);
    let congr_y = d.lemma(creal.add_congr, &[y_ny, zero, rest, rest, an_y, refl_rest]); // Equiv(y_ny_rest, zero_rest)
    let za_y = zero_add_proof(d, p, rest); // Equiv(zero_rest, rest)
    let inner = chain(
        d,
        p,
        y_nyrest,
        &[
            (y_ny_rest, assoc_y_symm),
            (zero_rest, congr_y),
            (rest, za_y),
        ],
    );
    // inner : Equiv(y_nyrest, rest)

    let x_nx_y_nyrest = cadd(d, p, nx, y_nyrest);
    let outer_lhs = cadd(d, p, x, x_nx_y_nyrest);
    let refl_nx = refl(d, p, nx);
    let nx_rest = cadd(d, p, nx, rest);
    let congr_inner = d.lemma(creal.add_congr, &[nx, nx, y_nyrest, rest, refl_nx, inner]); // Equiv(x_nx_y_nyrest, nx_rest)
    let x_nx_rest = cadd(d, p, x, nx_rest);
    let refl_x = refl(d, p, x);
    let congr_outer1 = d.lemma(
        creal.add_congr,
        &[x, x, x_nx_y_nyrest, nx_rest, refl_x, congr_inner],
    ); // Equiv(outer_lhs, x_nx_rest)
    let x_nx = cadd(d, p, x, nx);
    let x_nx_rest2 = cadd(d, p, x_nx, rest);
    let assoc_x = d.lemma(creal.add_assoc, &[x, nx, rest]); // Equiv(x_nx_rest2, x_nx_rest)
    let assoc_x_symm = symm(d, p, x_nx_rest2, x_nx_rest, assoc_x); // Equiv(x_nx_rest, x_nx_rest2)
    let an_x = d.lemma(creal.add_neg, &[x]); // Equiv(x_nx, zero)
    let congr_x = d.lemma(creal.add_congr, &[x_nx, zero, rest, rest, an_x, refl_rest]); // Equiv(x_nx_rest2, zero_rest2)
    let zero_rest2 = cadd(d, p, zero, rest);
    let za_x = zero_add_proof(d, p, rest); // Equiv(zero_rest2, rest)
    chain(
        d,
        p,
        outer_lhs,
        &[
            (x_nx_rest, congr_outer1),
            (x_nx_rest2, assoc_x_symm),
            (zero_rest2, congr_x),
            (rest, za_x),
        ],
    )
}

/// The scalar content of [`CPointPrelude::lagrange_identity`]. Returns
/// `(s1, s2, s3, proof)` where `s1 = (a²+b²)(c²+e²)`, `s2 = (ac+be)²`,
/// `s3 = (ae−bc)²`, and `proof : Equiv (add s1 (neg s2)) s3`.
fn lagrange_identity_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let creal = p.creal;
    let aa = cmul(d, p, a, a);
    let bb = cmul(d, p, b, b);
    let cc = cmul(d, p, c, c);
    let ee = cmul(d, p, e, e);
    let ac = cmul(d, p, a, c);
    let be = cmul(d, p, b, e);
    let ae = cmul(d, p, a, e);
    let bc = cmul(d, p, b, c);
    let nbc = cneg(d, p, bc);

    let (s1, chain1, proof_s1) = expand_mul_sum2(d, p, aa, bb, cc, ee);
    let (s2, chain2, proof_s2) = expand_mul_sum2(d, p, ac, be, ac, be);
    let (s3, chain3, proof_s3) = expand_mul_sum2(d, p, ae, nbc, ae, nbc);

    // chain1's leaves are already canonical: [a2c2, a2e2, b2c2, b2e2].
    let a2c2 = cmul(d, p, aa, cc);
    let a2e2 = cmul(d, p, aa, ee);
    let b2c2 = cmul(d, p, bb, cc);
    let b2e2 = cmul(d, p, bb, ee);

    let ab = cmul(d, p, a, b);
    let ce = cmul(d, p, c, e);
    let abce = cmul(d, p, ab, ce);
    let nabce = cneg(d, p, abce);

    // chain2's leaves: [ac*ac, ac*be, be*ac, be*be] -> canonical form.
    let ac_ac = cmul(d, p, ac, ac);
    let ac_be = cmul(d, p, ac, be);
    let be_ac = cmul(d, p, be, ac);
    let be_be = cmul(d, p, be, be);

    let p0_s2 = four_factor_swap_proof(d, p, a, c, a, c); // Equiv(ac_ac, a2c2)
    let p1_s2 = four_factor_swap_proof(d, p, a, c, b, e); // Equiv(ac_be, abce)
    let comm_be_ac = d.lemma(creal.mul_comm, &[be, ac]); // Equiv(be_ac, ac_be)
    let p2_s2 = chain(d, p, be_ac, &[(ac_be, comm_be_ac), (abce, p1_s2)]); // Equiv(be_ac, abce)
    let p3_s2 = four_factor_swap_proof(d, p, b, e, b, e); // Equiv(be_be, b2e2)

    let chain2_canon = rewrite_right_chain4(
        d, p, ac_ac, ac_be, be_ac, be_be, a2c2, abce, abce, b2e2, p0_s2, p1_s2, p2_s2, p3_s2,
    ); // Equiv(chain2, [a2c2,abce,abce,b2e2])
    let chain2_target = build_right_chain(d, p, &[a2c2, abce, abce, b2e2]);

    // chain3's leaves: [ae*ae, ae*nbc, nbc*ae, nbc*nbc] -> canonical form.
    let ae_ae = cmul(d, p, ae, ae);
    let ae_nbc = cmul(d, p, ae, nbc);
    let nbc_ae = cmul(d, p, nbc, ae);
    let nbc_nbc = cmul(d, p, nbc, nbc);

    let p0_s3 = four_factor_swap_proof(d, p, a, e, a, e); // Equiv(ae_ae, a2e2)

    let ae_bc = cmul(d, p, ae, bc);
    let mnr = mul_neg_right_proof(d, p, ae, bc); // Equiv(ae_nbc, neg ae_bc)
    let neg_ae_bc = cneg(d, p, ae_bc);
    let swap_ae_bc = four_factor_swap_proof(d, p, a, e, b, c); // Equiv(ae_bc, ab*ec)
    let ec = cmul(d, p, e, c);
    let ab_ec = cmul(d, p, ab, ec);
    let comm_ec = d.lemma(creal.mul_comm, &[e, c]); // Equiv(ec, ce)
    let refl_ab = refl(d, p, ab);
    let congr_ab = d.lemma(creal.mul_congr, &[ab, ab, ec, ce, refl_ab, comm_ec]); // Equiv(ab_ec, abce)
    let ae_bc_to_abce = chain(d, p, ae_bc, &[(ab_ec, swap_ae_bc), (abce, congr_ab)]); // Equiv(ae_bc, abce)
    let neg_congr_aebc = d.lemma(creal.neg_congr, &[ae_bc, abce, ae_bc_to_abce]); // Equiv(neg ae_bc, nabce)
    let p1_s3 = chain(d, p, ae_nbc, &[(neg_ae_bc, mnr), (nabce, neg_congr_aebc)]); // Equiv(ae_nbc, nabce)

    let comm_nbc_ae = d.lemma(creal.mul_comm, &[nbc, ae]); // Equiv(nbc_ae, ae_nbc)
    let p2_s3 = chain(d, p, nbc_ae, &[(ae_nbc, comm_nbc_ae), (nabce, p1_s3)]); // Equiv(nbc_ae, nabce)

    let nmn_step = d.lemma(creal.neg_mul_neg, &[bc]); // Equiv(nbc_nbc, bc*bc)
    let bc_bc = cmul(d, p, bc, bc);
    let swap_bcbc = four_factor_swap_proof(d, p, b, c, b, c); // Equiv(bc_bc, b2c2)
    let p3_s3 = chain(d, p, nbc_nbc, &[(bc_bc, nmn_step), (b2c2, swap_bcbc)]);

    let chain3_canon = rewrite_right_chain4(
        d, p, ae_ae, ae_nbc, nbc_ae, nbc_nbc, a2e2, nabce, nabce, b2c2, p0_s3, p1_s3, p2_s3, p3_s3,
    ); // Equiv(chain3, [a2e2,nabce,nabce,b2c2])
    let chain3_target = build_right_chain(d, p, &[a2e2, nabce, nabce, b2c2]);

    let proof_s2_full = chain(
        d,
        p,
        s2,
        &[(chain2, proof_s2), (chain2_target, chain2_canon)],
    ); // Equiv(s2, chain2_target)
    let proof_s3_full = chain(
        d,
        p,
        s3,
        &[(chain3, proof_s3), (chain3_target, chain3_canon)],
    ); // Equiv(s3, chain3_target)

    let neg_s2 = cneg(d, p, s2);
    let neg_chain2_target = cneg(d, p, chain2_target);
    let neg_s2_congr = d.lemma(creal.neg_congr, &[s2, chain2_target, proof_s2_full]); // Equiv(neg_s2, neg_chain2_target)
    let refl_chain1 = refl(d, p, chain1);
    let add_congr_1 = d.lemma(
        creal.add_congr,
        &[
            s1,
            chain1,
            neg_s2,
            neg_chain2_target,
            proof_s1,
            neg_s2_congr,
        ],
    ); // Equiv(add s1 neg_s2, add chain1 neg_chain2_target)
    let outer = cadd(d, p, chain1, neg_chain2_target);

    let neg_dist2 = neg_distribute_chain4(d, p, a2c2, abce, abce, b2e2);
    // Equiv(neg_chain2_target, [na2c2, nabce, nabce, nb2e2])
    let na2c2 = cneg(d, p, a2c2);
    let nb2e2 = cneg(d, p, b2e2);
    let neg_chain2_leaves = build_right_chain(d, p, &[na2c2, nabce, nabce, nb2e2]);
    let congr_outer_neg = d.lemma(
        creal.add_congr,
        &[
            chain1,
            chain1,
            neg_chain2_target,
            neg_chain2_leaves,
            refl_chain1,
            neg_dist2,
        ],
    ); // Equiv(outer, outer2)
    let outer2 = cadd(d, p, chain1, neg_chain2_leaves);

    let (concat_result, concat_proof) =
        concat_right_chains(d, p, &[a2c2, a2e2, b2c2, b2e2], neg_chain2_leaves);
    // concat_proof : Equiv(outer2, concat_result)

    let from_leaves = [a2c2, a2e2, b2c2, b2e2, na2c2, nabce, nabce, nb2e2];
    let to_leaves = [a2c2, na2c2, b2e2, nb2e2, a2e2, nabce, nabce, b2c2];
    let reorder_proof = reorder_right_chain(d, p, &from_leaves, &to_leaves);
    let reordered = build_right_chain(d, p, &to_leaves);

    let reduce_to_chain3 = cancel_two_pairs_prefix(d, p, a2c2, b2e2, chain3_target);
    // Equiv(reordered, chain3_target)

    let s3_from_chain3 = symm(d, p, s3, chain3_target, proof_s3_full); // Equiv(chain3_target, s3)

    let s1_diff = cadd(d, p, s1, neg_s2);
    let full = chain(
        d,
        p,
        s1_diff,
        &[
            (outer, add_congr_1),
            (outer2, congr_outer_neg),
            (concat_result, concat_proof),
            (reordered, reorder_proof),
            (chain3_target, reduce_to_chain3),
            (s3, s3_from_chain3),
        ],
    );
    (s1, s2, s3, full)
}

/// **Positive-semidefiniteness of `dot`.** See
/// [`CPointPrelude::dot_self_nonneg`].
fn declare_dot_self_nonneg(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let v_fv = d.fresh_fvar();
    let pv = d.kernel().fvar(v_fv);
    let vx = d.const_app(p.x, &[pv]);
    let vy = d.const_app(p.y, &[pv]);

    let vxvx = cmul(d, p, vx, vx);
    let vyvy = cmul(d, p, vy, vy);
    let sqx = d.lemma(creal.sq_nonneg, &[vx]); // le zero vxvx
    let sqy = d.lemma(creal.sq_nonneg, &[vy]); // le zero vyvy

    let zero = czero(d, p);
    let zero_zero = cadd(d, p, zero, zero);
    let az = d.lemma(creal.add_zero, &[zero]); // Equiv(zero_zero, zero)
    let az_symm = symm(d, p, zero_zero, zero, az); // Equiv(zero, zero_zero)
    let le_zero_zerozero = d.lemma(creal.le_of_equiv, &[zero, zero_zero, az_symm]); // le zero zero_zero

    let sum = cadd(d, p, vxvx, vyvy);
    let le_sum = d.lemma(creal.add_le_add, &[zero, vxvx, zero, vyvy, sqx, sqy]); // le zero_zero sum
    let result = d.lemma(
        creal.le_trans,
        &[zero, zero_zero, sum, le_zero_zerozero, le_sum],
    );
    // result : le zero sum, sum == dot pv pv by defeq of `dot`.

    let dot_vv = dotp(d, p, pv, pv);
    let ty_body = d.const_app(creal.le, &[zero, dot_vv]);
    let ty = d.pi_fv(v_fv, point, ty_body);
    let value = d.lam_fv(v_fv, point, result);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_self_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Lagrange's identity, in the plane.** See
/// [`CPointPrelude::lagrange_identity`].
fn declare_lagrange_identity(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let (s1, s2, s3, proof) = lagrange_identity_scalar_proof(d, p, a, b, c, e);
    let neg_s2 = cneg(d, p, s2);
    let lhs = cadd(d, p, s1, neg_s2);

    let ty_body = equiv(d, p, lhs, s3);
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
        name: p.lagrange_identity,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (add (add x (neg y)) y) x`.
fn sub_add_cancel_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    let creal = p.creal;
    let ny = cneg(d, p, y);
    let x_ny = cadd(d, p, x, ny);
    let lhs = cadd(d, p, x_ny, y);
    let ny_y = cadd(d, p, ny, y);
    let x_nyy = cadd(d, p, x, ny_y);
    let assoc = d.lemma(creal.add_assoc, &[x, ny, y]); // Equiv(lhs, x_nyy)
    let cancel = neg_add_cancel_proof(d, p, y); // Equiv(ny_y, zero)
    let refl_x = refl(d, p, x);
    let zero = czero(d, p);
    let congr = d.lemma(creal.add_congr, &[x, x, ny_y, zero, refl_x, cancel]); // Equiv(x_nyy, x_zero)
    let x_zero = cadd(d, p, x, zero);
    let az = d.lemma(creal.add_zero, &[x]); // Equiv(x_zero, x)
    chain(d, p, lhs, &[(x_nyy, assoc), (x_zero, congr), (x, az)])
}

/// Given `h : le zero (add x (neg y))`, produce `le y x`.
fn le_of_sub_nonneg(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ny = cneg(d, p, y);
    let x_ny = cadd(d, p, x, ny);
    let refl_y = d.lemma(creal.le_refl, &[y]);
    let zero = czero(d, p);
    let h2 = d.lemma(creal.add_le_add, &[zero, x_ny, y, y, h, refl_y]); // le (zero+y) (x_ny+y)
    let zero_y = cadd(d, p, zero, y);
    let x_ny_y = cadd(d, p, x_ny, y);
    let eq_left = zero_add_proof(d, p, y); // Equiv(zero_y, y)
    let eq_left_symm = symm(d, p, zero_y, y, eq_left); // Equiv(y, zero_y)
    let le_y_zeroy = d.lemma(creal.le_of_equiv, &[y, zero_y, eq_left_symm]); // le y zero_y
    let step1 = d.lemma(creal.le_trans, &[y, zero_y, x_ny_y, le_y_zeroy, h2]); // le y x_ny_y
    let eq_right = sub_add_cancel_proof(d, p, x, y); // Equiv(x_ny_y, x)
    let le_xnyy_x = d.lemma(creal.le_of_equiv, &[x_ny_y, x, eq_right]); // le x_ny_y x
    d.lemma(creal.le_trans, &[y, x_ny_y, x, step1, le_xnyy_x]) // le y x
}

/// **Cauchy-Schwarz, squared.** See [`CPointPrelude::cauchy_schwarz`].
fn declare_cauchy_schwarz(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let u_fv = d.fresh_fvar();
    let pu = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let pv = d.kernel().fvar(v_fv);

    let ux = d.const_app(p.x, &[pu]);
    let uy = d.const_app(p.y, &[pu]);
    let vx = d.const_app(p.x, &[pv]);
    let vy = d.const_app(p.y, &[pv]);

    let (s1, s2, s3, lagrange) = lagrange_identity_scalar_proof(d, p, ux, uy, vx, vy);

    let ae = cmul(d, p, ux, vy);
    let bc = cmul(d, p, uy, vx);
    let nbc = cneg(d, p, bc);
    let w = cadd(d, p, ae, nbc);
    let sq_w = d.lemma(creal.sq_nonneg, &[w]); // le zero s3 (s3 == mul w w)

    let neg_s2 = cneg(d, p, s2);
    let diff = cadd(d, p, s1, neg_s2);
    let lagrange_symm = symm(d, p, diff, s3, lagrange); // Equiv(s3, diff)
    let le_s3_diff = d.lemma(creal.le_of_equiv, &[s3, diff, lagrange_symm]); // le s3 diff
    let zero = czero(d, p);
    let le_zero_diff = d.lemma(creal.le_trans, &[zero, s3, diff, sq_w, le_s3_diff]); // le zero diff
    let le_s2_s1 = le_of_sub_nonneg(d, p, s1, s2, le_zero_diff); // le s2 s1

    let dot_uv = dotp(d, p, pu, pv);
    let dot_uu = dotp(d, p, pu, pu);
    let dot_vv = dotp(d, p, pv, pv);
    let lhs_ty = cmul(d, p, dot_uv, dot_uv);
    let rhs_ty = cmul(d, p, dot_uu, dot_vv);
    let ty_body = d.const_app(creal.le, &[lhs_ty, rhs_ty]);
    let ty = {
        let inner = d.pi_fv(v_fv, point, ty_body);
        d.pi_fv(u_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(v_fv, point, le_s2_s1);
        d.lam_fv(u_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cauchy_schwarz,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.Equiv (sub A C) (add (sub A B) (sub B C))` — point-level
/// telescoping, per-coordinate via [`telescope_scalar_proof`] and
/// [`and_intro`].
fn point_sub_telescope_fact(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    pa: ExprId,
    pb: ExprId,
    pc: ExprId,
) -> ExprId {
    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);

    let core_x = telescope_scalar_proof(d, p, ax, bx, cx);
    let core_y = telescope_scalar_proof(d, p, ay, by, cy);

    let claim_x = {
        let neg_cx = cneg(d, p, cx);
        let lhs = cadd(d, p, ax, neg_cx);
        let neg_bx = cneg(d, p, bx);
        let ab_x = cadd(d, p, ax, neg_bx);
        let bc_x = cadd(d, p, bx, neg_cx);
        let rhs = cadd(d, p, ab_x, bc_x);
        equiv(d, p, lhs, rhs)
    };
    let claim_y = {
        let neg_cy = cneg(d, p, cy);
        let lhs = cadd(d, p, ay, neg_cy);
        let neg_by = cneg(d, p, by);
        let ab_y = cadd(d, p, ay, neg_by);
        let bc_y = cadd(d, p, by, neg_cy);
        let rhs = cadd(d, p, ab_y, bc_y);
        equiv(d, p, lhs, rhs)
    };
    and_intro(d, p, claim_x, claim_y, core_x, core_y)
}

/// Given `uu = dot U U`, `uv = dot U V`, `vv = dot V V`, and
/// `h0 : le zero (add uu (add (neg uv) (add (neg uv) vv)))`, produce
/// `le (add uv uv) (add uu vv)` — `2·(U·V) ≤ U·U + V·V`.
fn two_uv_le_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    uu: ExprId,
    uv: ExprId,
    vv: ExprId,
    h0: ExprId,
) -> ExprId {
    let creal = p.creal;
    let nuv = cneg(d, p, uv);
    let big_q = cadd(d, p, uv, uv);
    let big_p = cadd(d, p, uu, vv);
    let neg_q = cneg(d, p, big_q);
    let p_negq = cadd(d, p, big_p, neg_q);

    let nd = neg_add_proof(d, p, uv, uv); // Equiv(neg_q, add nuv nuv)
    let nuv_nuv = cadd(d, p, nuv, nuv);
    let refl_p = refl(d, p, big_p);
    let step_a = d.lemma(creal.add_congr, &[big_p, big_p, neg_q, nuv_nuv, refl_p, nd]); // Equiv(p_negq, nested)
    let nested = cadd(d, p, big_p, nuv_nuv);

    let tree = sadd(
        sadd(SumTree::Leaf(uu), SumTree::Leaf(vv)),
        sadd(SumTree::Leaf(nuv), SumTree::Leaf(nuv)),
    );
    let (chain_res, flat_proof) = flatten_sum_tree(d, p, &tree); // Equiv(nested, chain_res)

    let target_leaves = [uu, nuv, nuv, vv];
    let reorder_proof = reorder_right_chain(d, p, &[uu, vv, nuv, nuv], &target_leaves);
    let target_chain = build_right_chain(d, p, &target_leaves);

    let rearrange_fwd = chain(
        d,
        p,
        p_negq,
        &[
            (nested, step_a),
            (chain_res, flat_proof),
            (target_chain, reorder_proof),
        ],
    ); // Equiv(p_negq, target_chain)
    let rearrange = symm(d, p, p_negq, target_chain, rearrange_fwd); // Equiv(target_chain, p_negq)

    let zero = czero(d, p);
    let le_of_equiv_step = d.lemma(creal.le_of_equiv, &[target_chain, p_negq, rearrange]); // le target_chain p_negq
    let le_zero_pnegq = d.lemma(
        creal.le_trans,
        &[zero, target_chain, p_negq, h0, le_of_equiv_step],
    ); // le zero p_negq

    le_of_sub_nonneg(d, p, big_p, big_q, le_zero_pnegq) // le big_q big_p
}

/// **The triangle inequality for `distSq`, factor-2 form.** See
/// [`CPointPrelude::dist_sq_double_sum_bound`].
fn declare_dist_sq_double_sum_bound(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let u = psub(d, p, pa, pb); // U = A - B
    let v = psub(d, p, pb, pc); // V = B - C
    let w = psub(d, p, u, v); // W = U - V

    let uu = dotp(d, p, u, u);
    let uv = dotp(d, p, u, v);
    let vv = dotp(d, p, v, v);

    // 0 <= dot W W
    let dsn = d.lemma(p.dot_self_nonneg, &[w]); // le zero (dot W W)
    let dss = d.lemma(p.dot_self_sub, &[u, v]); // Equiv(dot W W, add uu (add (neg uv)(add (neg uv) vv)))
    let neg_uv = cneg(d, p, uv);
    let neg_uv_vv = cadd(d, p, neg_uv, vv);
    let neg_uv_neg_uv_vv = cadd(d, p, neg_uv, neg_uv_vv);
    let target0 = cadd(d, p, uu, neg_uv_neg_uv_vv);
    let dot_ww = dotp(d, p, w, w);
    let le_of_equiv_dss = d.lemma(creal.le_of_equiv, &[dot_ww, target0, dss]); // le dot_ww target0
    let zero = czero(d, p);
    let h0 = d.lemma(
        creal.le_trans,
        &[zero, dot_ww, target0, dsn, le_of_equiv_dss],
    ); // le zero target0

    let le_2uv = two_uv_le_proof(d, p, uu, uv, vv, h0); // le (add uv uv) (add uu vv)

    // distSq A C ~ dot(sub A C)(sub A C) ~ dot(add U V)(add U V)
    //            ~ add uu (add uv (add uv vv))  [dot_self_add]
    let ac_sub = psub(d, p, pa, pc);
    let add_uv = padd(d, p, u, v);
    let telescope = point_sub_telescope_fact(d, p, pa, pb, pc); // CPoint.Equiv (sub A C) (add U V)
    let dot_congr_step = d.lemma(
        p.dot_congr,
        &[ac_sub, add_uv, ac_sub, add_uv, telescope, telescope],
    ); // Equiv(dot(ac_sub,ac_sub), dot(add_uv,add_uv))
    let dsa = d.lemma(p.dot_self_add, &[u, v]); // Equiv(dot(add_uv,add_uv), add uu (add uv (add uv vv)))
    let dist_ac = d.const_app(p.dist_sq, &[pa, pc]);
    let dot_acac = dotp(d, p, ac_sub, ac_sub);
    let dot_uvuv = dotp(d, p, add_uv, add_uv);
    let uv_vv = cadd(d, p, uv, vv);
    let uv_uv_vv = cadd(d, p, uv, uv_vv);
    let expanded = cadd(d, p, uu, uv_uv_vv);
    let dist_ac_to_expanded = chain(
        d,
        p,
        dot_acac,
        &[(dot_uvuv, dot_congr_step), (expanded, dsa)],
    ); // Equiv(dist_ac, expanded)  (dist_ac defeq dot_acac)

    // le expanded (add (add uu vv) (add uu vv))
    // expanded = uu + (uv + (uv + vv)); rearrange to (uv+uv) + (uu+vv), then bound uv+uv.
    let sum_uu_vv = cadd(d, p, uu, vv);
    let double_sum = cadd(d, p, sum_uu_vv, sum_uu_vv);
    let uv_uv = cadd(d, p, uv, uv);

    let expand_tree = sadd(
        SumTree::Leaf(uu),
        sadd(
            SumTree::Leaf(uv),
            sadd(SumTree::Leaf(uv), SumTree::Leaf(vv)),
        ),
    );
    let (expand_chain, expand_flat) = flatten_sum_tree(d, p, &expand_tree);
    // expand_chain leaves: [uu, uv, uv, vv]
    let reordered_leaves = [uv, uv, uu, vv];
    let reorder_expand = reorder_right_chain(d, p, &[uu, uv, uv, vv], &reordered_leaves);
    let reordered_expand_chain = build_right_chain(d, p, &reordered_leaves);
    let expanded_to_reordered = chain(
        d,
        p,
        expanded,
        &[
            (expand_chain, expand_flat),
            (reordered_expand_chain, reorder_expand),
        ],
    ); // Equiv(expanded, uv+(uv+(uu+vv)))

    // uv + (uv + (uu+vv)) ~ (uv+uv) + (uu+vv)  [add_assoc, reversed]
    let uu_vv = cadd(d, p, uu, vv);
    let uv_uv_uuvv = cadd(d, p, uv_uv, uu_vv);
    let assoc_final = d.lemma(creal.add_assoc, &[uv, uv, uu_vv]); // Equiv(uv_uv_uuvv, reordered_expand_chain)
    let assoc_final_symm = symm(d, p, uv_uv_uuvv, reordered_expand_chain, assoc_final);

    let expanded_to_grouped = chain(
        d,
        p,
        expanded,
        &[
            (reordered_expand_chain, expanded_to_reordered),
            (uv_uv_uuvv, assoc_final_symm),
        ],
    ); // Equiv(expanded, uv_uv_uuvv)

    let le_refl_uuvv = d.lemma(creal.le_refl, &[uu_vv]);
    let le_grouped = d.lemma(
        creal.add_le_add,
        &[uv_uv, uu_vv, uu_vv, uu_vv, le_2uv, le_refl_uuvv],
    ); // le uv_uv_uuvv (uu_vv + uu_vv) = le uv_uv_uuvv double_sum

    let le_of_equiv_expanded = d.lemma(
        creal.le_of_equiv,
        &[expanded, uv_uv_uuvv, expanded_to_grouped],
    );
    let le_expanded_double = d.lemma(
        creal.le_trans,
        &[
            expanded,
            uv_uv_uuvv,
            double_sum,
            le_of_equiv_expanded,
            le_grouped,
        ],
    ); // le expanded double_sum

    let le_of_equiv_dist = d.lemma(creal.le_of_equiv, &[dist_ac, expanded, dist_ac_to_expanded]); // le dist_ac expanded
    let result = d.lemma(
        creal.le_trans,
        &[
            dist_ac,
            expanded,
            double_sum,
            le_of_equiv_dist,
            le_expanded_double,
        ],
    ); // le dist_ac double_sum

    // State the type via the named `distSq`, not the raw `dot`/`sub` shape
    // `double_sum` is built from; `value` (built over `uu`/`vv`) still
    // type-checks against it by the same defeq unfolding
    // `declare_pythagoras_dist_sq` relies on.
    let dist_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dist_bc = d.const_app(p.dist_sq, &[pb, pc]);
    let sum_dist_ty = cadd(d, p, dist_ab, dist_bc);
    let double_sum_ty = cadd(d, p, sum_dist_ty, sum_dist_ty);
    let ty_body = d.const_app(creal.le, &[dist_ac, double_sum_ty]);
    let ty = {
        let w2 = d.pi_fv(c_fv, point, ty_body);
        let w1 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(a_fv, point, w1)
    };
    let value = {
        let w2 = d.lam_fv(c_fv, point, result);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dist_sq_double_sum_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Euclid I.20, squared — the honest triangle inequality.** See
/// [`CPointPrelude::dist_sq_triangle_sq_bound`].
///
/// With `U := sub A B`, `V := sub B C`: `distSq A C ~ dot(U,U) + (dot(U,V) +
/// (dot(U,V) + dot(V,V)))` ([`declare_dist_sq`]'s definitional unfolding plus
/// [`point_sub_telescope_fact`]/[`CPointPrelude::dot_self_add`], exactly the
/// derivation [`declare_dist_sq_double_sum_bound`] already builds), while
/// `distSq A B` and `distSq B C` unfold *directly* (no telescoping needed —
/// `U`/`V` themselves are `sub A B`/`sub B C`) to `dot(U,U)` and `dot(V,V)`.
/// So `distSq A C − distSq A B − distSq B C` is, term-for-term, `dot(U,V) +
/// dot(U,V)` — proved by flattening both sides into a 6-leaf right-chain
/// `[dot(U,U), dot(U,V), dot(U,V), dot(V,V), neg dot(U,U), neg dot(V,V)]` and
/// cancelling the two opposite pairs with [`cancel_two_pairs_prefix`].
/// Squaring that identity and bounding the cross term via
/// [`CPointPrelude::cauchy_schwarz`] (`dot(U,V)·dot(U,V) ≤ dot(U,U)·dot(V,V)
/// = distSq A B · distSq B C`) gives the statement below — `(x−a−c)² ≤ 4ac`
/// for `x = distSq A C`, `a = distSq A B`, `c = distSq B C`, exactly Lagrange
/// applied to the two edge vectors.
fn declare_dist_sq_triangle_sq_bound(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let u = psub(d, p, pa, pb); // U = A - B
    let v = psub(d, p, pb, pc); // V = B - C

    let uu = dotp(d, p, u, u);
    let uv = dotp(d, p, u, v);
    let vv = dotp(d, p, v, v);

    // distSq A C ~ dot(add U V)(add U V) ~ uu + (uv + (uv + vv))
    // — the same telescoping [`declare_dist_sq_double_sum_bound`] uses.
    let ac_sub = psub(d, p, pa, pc);
    let add_uv = padd(d, p, u, v);
    let telescope = point_sub_telescope_fact(d, p, pa, pb, pc); // CPoint.Equiv (sub A C) (add U V)
    let dot_congr_step = d.lemma(
        p.dot_congr,
        &[ac_sub, add_uv, ac_sub, add_uv, telescope, telescope],
    ); // Equiv(dot(ac_sub,ac_sub), dot(add_uv,add_uv))
    let dsa = d.lemma(p.dot_self_add, &[u, v]); // Equiv(dot(add_uv,add_uv), add uu (add uv (add uv vv)))
    let dot_acac = dotp(d, p, ac_sub, ac_sub); // == distSq A C, by defeq
    let dot_uvuv = dotp(d, p, add_uv, add_uv);
    let uv_vv = cadd(d, p, uv, vv);
    let uv_uv_vv = cadd(d, p, uv, uv_vv);
    let expanded = cadd(d, p, uu, uv_uv_vv);
    let dist_ac_to_expanded = chain(
        d,
        p,
        dot_acac,
        &[(dot_uvuv, dot_congr_step), (expanded, dsa)],
    ); // Equiv(dot_acac, expanded)

    // diff_raw = (distSq A C - distSq A B) - distSq B C, in raw dot terms
    // (distSq A B / distSq B C unfold directly to uu / vv here — no
    // telescoping needed, unlike distSq A C).
    let neg_uu = cneg(d, p, uu);
    let neg_vv = cneg(d, p, vv);
    let ac_minus_ab = cadd(d, p, dot_acac, neg_uu);
    let diff_raw = cadd(d, p, ac_minus_ab, neg_vv);

    // Replace dot_acac by its expansion inside diff_raw.
    let refl_neg_uu = refl(d, p, neg_uu);
    let congr1 = d.lemma(
        creal.add_congr,
        &[
            dot_acac,
            expanded,
            neg_uu,
            neg_uu,
            dist_ac_to_expanded,
            refl_neg_uu,
        ],
    ); // Equiv(ac_minus_ab, expanded_minus_ab)
    let expanded_minus_ab = cadd(d, p, expanded, neg_uu);
    let refl_neg_vv = refl(d, p, neg_vv);
    let congr2 = d.lemma(
        creal.add_congr,
        &[
            ac_minus_ab,
            expanded_minus_ab,
            neg_vv,
            neg_vv,
            congr1,
            refl_neg_vv,
        ],
    ); // Equiv(diff_raw, diff_expanded)
    let diff_expanded = cadd(d, p, expanded_minus_ab, neg_vv);

    // Flatten diff_expanded's 6 leaves [uu, uv, uv, vv, neg_uu, neg_vv],
    // reorder to bring the two cancelling pairs to the front, then cancel.
    let tree = sadd(
        sadd(
            sadd(
                SumTree::Leaf(uu),
                sadd(
                    SumTree::Leaf(uv),
                    sadd(SumTree::Leaf(uv), SumTree::Leaf(vv)),
                ),
            ),
            SumTree::Leaf(neg_uu),
        ),
        SumTree::Leaf(neg_vv),
    );
    let (chain6, flat_proof) = flatten_sum_tree(d, p, &tree); // Equiv(diff_expanded, chain6)

    let from_leaves = [uu, uv, uv, vv, neg_uu, neg_vv];
    let target_leaves = [uu, neg_uu, vv, neg_vv, uv, uv];
    let reorder_proof = reorder_right_chain(d, p, &from_leaves, &target_leaves);
    let reordered_chain = build_right_chain(d, p, &target_leaves);

    let uv_plus_uv = cadd(d, p, uv, uv);
    let cancel_proof = cancel_two_pairs_prefix(d, p, uu, vv, uv_plus_uv);
    // Equiv(reordered_chain, uv_plus_uv)

    let diff_raw_to_uvpp = chain(
        d,
        p,
        diff_raw,
        &[
            (diff_expanded, congr2),
            (chain6, flat_proof),
            (reordered_chain, reorder_proof),
            (uv_plus_uv, cancel_proof),
        ],
    ); // Equiv(diff_raw, uv_plus_uv)

    // (diff_raw)^2 ~ (uv+uv)^2 ~ uv*uv + (uv*uv + (uv*uv + uv*uv))  [Cauchy-Schwarz bounds each uv*uv]
    let mul_diff_diff = cmul(d, p, diff_raw, diff_raw);
    let mul_uvpp_uvpp = cmul(d, p, uv_plus_uv, uv_plus_uv);
    let mul_congr_diff = d.lemma(
        creal.mul_congr,
        &[
            diff_raw,
            uv_plus_uv,
            diff_raw,
            uv_plus_uv,
            diff_raw_to_uvpp,
            diff_raw_to_uvpp,
        ],
    ); // Equiv(mul_diff_diff, mul_uvpp_uvpp)

    let (_orig, chain4_uvuv, expand_proof) = expand_mul_sum2(d, p, uv, uv, uv, uv);
    // expand_proof : Equiv(mul_uvpp_uvpp, chain4_uvuv)

    let mul_diff_diff_to_chain4 = chain(
        d,
        p,
        mul_diff_diff,
        &[(mul_uvpp_uvpp, mul_congr_diff), (chain4_uvuv, expand_proof)],
    ); // Equiv(mul_diff_diff, chain4_uvuv)

    let uvuv = cmul(d, p, uv, uv);
    let ac_prod = cmul(d, p, uu, vv);
    let cs = d.lemma(p.cauchy_schwarz, &[u, v]); // le uvuv ac_prod

    let level1 = d.lemma(creal.add_le_add, &[uvuv, ac_prod, uvuv, ac_prod, cs, cs]);
    let uvuv_uvuv = cadd(d, p, uvuv, uvuv);
    let acprod_acprod = cadd(d, p, ac_prod, ac_prod);
    // level1 : le uvuv_uvuv acprod_acprod

    let level2 = d.lemma(
        creal.add_le_add,
        &[uvuv, ac_prod, uvuv_uvuv, acprod_acprod, cs, level1],
    );
    let three_uvuv = cadd(d, p, uvuv, uvuv_uvuv);
    let three_acprod = cadd(d, p, ac_prod, acprod_acprod);
    // level2 : le three_uvuv three_acprod

    let level3 = d.lemma(
        creal.add_le_add,
        &[uvuv, ac_prod, three_uvuv, three_acprod, cs, level2],
    );
    let chain4_acprod = cadd(d, p, ac_prod, three_acprod);
    // level3 : le chain4_uvuv chain4_acprod  (chain4_uvuv == cadd(uvuv, three_uvuv))

    let le_of_equiv_step = d.lemma(
        creal.le_of_equiv,
        &[mul_diff_diff, chain4_uvuv, mul_diff_diff_to_chain4],
    ); // le mul_diff_diff chain4_uvuv
    let final_le = d.lemma(
        creal.le_trans,
        &[
            mul_diff_diff,
            chain4_uvuv,
            chain4_acprod,
            le_of_equiv_step,
            level3,
        ],
    ); // le mul_diff_diff chain4_acprod

    // State via the named `distSq`, not the raw `dot`/`sub` shape `value` is
    // built over — the same defeq bridge `declare_dist_sq_double_sum_bound`
    // and `declare_pythagoras_dist_sq` rely on.
    let dist_ac = d.const_app(p.dist_sq, &[pa, pc]);
    let dist_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dist_bc = d.const_app(p.dist_sq, &[pb, pc]);
    let neg_dist_ab = cneg(d, p, dist_ab);
    let neg_dist_bc = cneg(d, p, dist_bc);
    let ac_minus_ab_ty = cadd(d, p, dist_ac, neg_dist_ab);
    let diff_ty = cadd(d, p, ac_minus_ab_ty, neg_dist_bc);
    let mul_diff_diff_ty = cmul(d, p, diff_ty, diff_ty);
    let ab_bc = cmul(d, p, dist_ab, dist_bc);
    let ab_bc_pair = cadd(d, p, ab_bc, ab_bc);
    let ab_bc_triple = cadd(d, p, ab_bc, ab_bc_pair);
    let sum4_ty = cadd(d, p, ab_bc, ab_bc_triple);
    let ty_body = d.const_app(creal.le, &[mul_diff_diff_ty, sum4_ty]);

    let ty = {
        let w2 = d.pi_fv(c_fv, point, ty_body);
        let w1 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(a_fv, point, w1)
    };
    let value = {
        let w2 = d.lam_fv(c_fv, point, final_le);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dist_sq_triangle_sq_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.mk CReal.zero CReal.zero` — the zero point, built directly from
/// the constructor rather than a named constant (there is no `CPoint.zero`
/// in this prelude): `x`/`y` applied to it reduce by iota to `CReal.zero`,
/// which is what lets the theorems below state their conclusion over it and
/// have a per-coordinate `Equiv _ CReal.zero` proof close it by defeq — the
/// same maneuver `complex.rs`'s `eq_zero_of_normSq_eq_zero` uses against its
/// own `zero_c`.
fn zero_point(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    let zero = czero(d, p);
    d.const_app(p.mk, &[zero, zero])
}

/// `CPoint.dot_self_zero_of_eq_zero`: the **easy** half of `dot V V ~ 0 ↔ V ~
/// 0`. The converse is [`declare_eq_zero_of_dot_self_zero`], just below.
/// Mirrors `declare_norm_sq_eq_zero_of_eq_zero` in `complex.rs`.
fn declare_dot_self_zero_of_eq_zero(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let point = point_ty(d, p);

    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let zp = zero_point(d, p);
    let hypothesis = d.const_app(p.point_equiv, &[v, zp]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let vx = d.const_app(p.x, &[v]);
    let vy = d.const_app(p.y, &[v]);
    let zx = d.const_app(p.x, &[zp]);
    let zy = d.const_app(p.y, &[zp]);
    let ex_ty = equiv(d, p, vx, zx);
    let ey_ty = equiv(d, p, vy, zy);
    let hx = d.and_left(ex_ty, ey_ty, h);
    let hy = d.and_right(ex_ty, ey_ty, h);
    // hx : Equiv vx zx, hy : Equiv vy zy, both defeq Equiv _ CReal.zero.

    let zero = czero(d, p);
    let aa_eq = d.lemma(creal.mul_congr, &[vx, zero, vx, zero, hx, hx]);
    let bb_eq = d.lemma(creal.mul_congr, &[vy, zero, vy, zero, hy, hy]);
    let vxvx = cmul(d, p, vx, vx);
    let vyvy = cmul(d, p, vy, vy);
    let mul_zero_term = cmul(d, p, zero, zero);
    let sum_eq = d.lemma(
        creal.add_congr,
        &[vxvx, mul_zero_term, vyvy, mul_zero_term, aa_eq, bb_eq],
    );
    // sum_eq : Equiv (add vxvx vyvy) (add mul_zero_term mul_zero_term)

    let mz = d.lemma(creal.mul_zero, &[zero]); // Equiv mul_zero_term zero
    let add_cong = d.lemma(
        creal.add_congr,
        &[mul_zero_term, zero, mul_zero_term, zero, mz, mz],
    ); // Equiv (add mul_zero_term mul_zero_term) (add zero zero)
    let az = d.lemma(creal.add_zero, &[zero]); // Equiv (add zero zero) zero
    let zero_zero = cadd(d, p, zero, zero);
    let collapse = d.lemma(
        creal.equiv_trans,
        &[mul_zero_term, zero_zero, zero, add_cong, az],
    );
    // collapse : Equiv (add mul_zero_term mul_zero_term) zero

    let sum = cadd(d, p, vxvx, vyvy);
    let mul_zero_sum = cadd(d, p, mul_zero_term, mul_zero_term);
    let proof = d.lemma(
        creal.equiv_trans,
        &[sum, mul_zero_sum, zero, sum_eq, collapse],
    );
    // proof : Equiv (add vxvx vyvy) zero, and `dot V V` is defeq to that sum.

    let dot_vv = dotp(d, p, v, v);
    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        d.lam_fv(v_fv, point, with_h)
    };
    let ty = {
        let claim = equiv(d, p, dot_vv, zero);
        let inner = d.arrow(hypothesis, claim);
        d.pi_fv(v_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_self_zero_of_eq_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.eq_zero_of_dot_self_zero`: the **converse** half of `dot V V ~ 0
/// ↔ V ~ 0` — the content. Mirrors `declare_eq_zero_of_norm_sq_eq_zero` in
/// `complex.rs`, but where that file needed its own `nonneg_sum_zero_left`
/// helper, this one uses the kernel theorem
/// [`CRealPrelude::eq_zero_of_add_eq_zero_of_nonneg`](crate::CRealPrelude::eq_zero_of_add_eq_zero_of_nonneg)
/// directly.
fn declare_eq_zero_of_dot_self_zero(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let point = point_ty(d, p);

    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let vx = d.const_app(p.x, &[v]);
    let vy = d.const_app(p.y, &[v]);
    let zero = czero(d, p);

    let vxvx = cmul(d, p, vx, vx);
    let vyvy = cmul(d, p, vy, vy);
    let dot_vv = dotp(d, p, v, v); // defeq to `add vxvx vyvy`

    let hypothesis = equiv(d, p, dot_vv, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let aa_nonneg = d.lemma(creal.sq_nonneg, &[vx]); // le zero vxvx
    let bb_nonneg = d.lemma(creal.sq_nonneg, &[vy]); // le zero vyvy

    let vxvx_zero = d.lemma(
        creal.eq_zero_of_add_eq_zero_of_nonneg,
        &[vxvx, vyvy, aa_nonneg, bb_nonneg, h],
    ); // Equiv vxvx zero

    // For vyvy, the sum needs to be read in the other order.
    let vyvy_vxvx = cadd(d, p, vyvy, vxvx);
    let vxvx_vyvy = cadd(d, p, vxvx, vyvy);
    let comm = d.lemma(creal.add_comm, &[vyvy, vxvx]); // Equiv(add vyvy vxvx, add vxvx vyvy)
    let h_swapped = d.lemma(creal.equiv_trans, &[vyvy_vxvx, vxvx_vyvy, zero, comm, h]);
    let vyvy_zero = d.lemma(
        creal.eq_zero_of_add_eq_zero_of_nonneg,
        &[vyvy, vxvx, bb_nonneg, aa_nonneg, h_swapped],
    ); // Equiv vyvy zero

    let vx_zero = d.lemma(creal.eq_zero_of_mul_self_zero, &[vx, vxvx_zero]);
    let vy_zero = d.lemma(creal.eq_zero_of_mul_self_zero, &[vy, vyvy_zero]);

    let zp = zero_point(d, p);
    let zx = d.const_app(p.x, &[zp]);
    let zy = d.const_app(p.y, &[zp]);
    let left_claim = equiv(d, p, vx, zx);
    let right_claim = equiv(d, p, vy, zy);
    let body = and_intro(d, p, left_claim, right_claim, vx_zero, vy_zero);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        d.lam_fv(v_fv, point, with_h)
    };
    let ty = {
        let claim = d.const_app(p.point_equiv, &[v, zp]);
        let inner = d.arrow(hypothesis, claim);
        d.pi_fv(v_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.eq_zero_of_dot_self_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.dot_self_zero_iff`: the biconditional, from
/// [`declare_eq_zero_of_dot_self_zero`] (`mp`) and
/// [`declare_dot_self_zero_of_eq_zero`] (`mpr`) — a restatement, not a new
/// proof, in the style [`declare_pythagoras_dist_sq`] uses: each half is the
/// existing theorem re-applied as a value. Mirrors
/// `declare_norm_sq_eq_zero_iff` in `complex.rs`.
fn declare_dot_self_zero_iff(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let logic = creal.rat.int.logic;
    let point = point_ty(d, p);

    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let zero = czero(d, p);
    let zp = zero_point(d, p);
    let dot_vv = dotp(d, p, v, v);

    let dot_stmt = equiv(d, p, dot_vv, zero);
    let point_stmt = d.const_app(p.point_equiv, &[v, zp]);

    // mp : Equiv (dot V V) zero -> CPoint.Equiv V zero_point
    let mp_body = d.lemma(p.eq_zero_of_dot_self_zero, &[v]);
    // mpr : CPoint.Equiv V zero_point -> Equiv (dot V V) zero
    let mpr_body = d.lemma(p.dot_self_zero_of_eq_zero, &[v]);

    let iff_stmt = d.const_app(logic.iff, &[dot_stmt, point_stmt]);
    let iff_proof = d.const_app(logic.iff_intro, &[dot_stmt, point_stmt, mp_body, mpr_body]);

    let value = d.lam_fv(v_fv, point, iff_proof);
    let ty = d.pi_fv(v_fv, point, iff_stmt);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_self_zero_iff,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (add u (neg v)) CReal.zero`, from `h : Equiv u v` — a ring fact,
/// not `CReal`-specific: `add_congr h (refl (neg v))` gives `Equiv (add u
/// (neg v)) (add v (neg v))`, and `add_neg` collapses the right side.
fn sub_eq_zero_of_equiv(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    u: ExprId,
    v: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let neg_v = cneg(d, p, v);
    let refl_negv = refl(d, p, neg_v);
    let u_negv = cadd(d, p, u, neg_v);
    let v_negv = cadd(d, p, v, neg_v);
    let congr = d.lemma(creal.add_congr, &[u, v, neg_v, neg_v, h, refl_negv]);
    // congr : Equiv u_negv v_negv
    let an = d.lemma(creal.add_neg, &[v]); // Equiv v_negv zero
    let zero = czero(d, p);
    chain(d, p, u_negv, &[(v_negv, congr), (zero, an)])
}

/// `Equiv u v`, from `h : Equiv (add u (neg v)) CReal.zero` — the converse
/// of [`sub_eq_zero_of_equiv`]. Route: `u ~ (add u (neg v)) + v`
/// ([`sub_add_cancel_proof`], reversed) `~ zero + v` (`add_congr h (refl
/// v)`) `~ v` ([`zero_add_proof`]).
fn equiv_of_sub_eq_zero(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    u: ExprId,
    v: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let neg_v = cneg(d, p, v);
    let u_negv = cadd(d, p, u, neg_v);
    let u_negv_v = cadd(d, p, u_negv, v);
    let cancel = sub_add_cancel_proof(d, p, u, v); // Equiv u_negv_v u
    let cancel_symm = symm(d, p, u_negv_v, u, cancel); // Equiv u u_negv_v
    let refl_v = refl(d, p, v);
    let zero = czero(d, p);
    let congr = d.lemma(creal.add_congr, &[u_negv, zero, v, v, h, refl_v]);
    // congr : Equiv u_negv_v (add zero v)
    let zero_v = cadd(d, p, zero, v);
    let za = zero_add_proof(d, p, v); // Equiv zero_v v
    chain(
        d,
        p,
        u,
        &[(u_negv_v, cancel_symm), (zero_v, congr), (v, za)],
    )
}

/// `CPoint.distSq_eq_zero_of_equiv`: the **easy** half of `distSq A B ~ 0 ↔
/// A ~ B`. A specialization of [`declare_dot_self_zero_of_eq_zero`] at
/// `V := CPoint.sub A B`.
fn declare_dist_sq_eq_zero_of_equiv(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);

    let hypothesis = d.const_app(p.point_equiv, &[pa, pb]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let ex_ty = equiv(d, p, ax, bx);
    let ey_ty = equiv(d, p, ay, by);
    let hx = d.and_left(ex_ty, ey_ty, h);
    let hy = d.and_right(ex_ty, ey_ty, h);

    let dx_zero = sub_eq_zero_of_equiv(d, p, ax, bx, hx); // Equiv (x (sub A B)) zero, defeq
    let dy_zero = sub_eq_zero_of_equiv(d, p, ay, by, hy); // Equiv (y (sub A B)) zero, defeq

    let sub_ab = psub(d, p, pa, pb);
    let dx = d.const_app(p.x, &[sub_ab]);
    let dy = d.const_app(p.y, &[sub_ab]);
    let zp = zero_point(d, p);
    let zx = d.const_app(p.x, &[zp]);
    let zy = d.const_app(p.y, &[zp]);
    let left_claim = equiv(d, p, dx, zx);
    let right_claim = equiv(d, p, dy, zy);
    let point_h = and_intro(d, p, left_claim, right_claim, dx_zero, dy_zero);
    // point_h : CPoint.Equiv sub_ab zero_point

    let proof = d.lemma(p.dot_self_zero_of_eq_zero, &[sub_ab, point_h]);
    // proof : Equiv (dot sub_ab sub_ab) zero, and `distSq A B` is defeq to
    // that.

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        let with_pb = d.lam_fv(pb_fv, point, with_h);
        d.lam_fv(pa_fv, point, with_pb)
    };
    let ty = {
        let dist_ab = d.const_app(p.dist_sq, &[pa, pb]);
        let zero = czero(d, p);
        let claim = equiv(d, p, dist_ab, zero);
        let inner = d.arrow(hypothesis, claim);
        let with_pb = d.pi_fv(pb_fv, point, inner);
        d.pi_fv(pa_fv, point, with_pb)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dist_sq_eq_zero_of_equiv,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.eq_zero_of_distSq_eq_zero`: the **converse** half of `distSq A B
/// ~ 0 ↔ A ~ B` — the content. A specialization of
/// [`declare_eq_zero_of_dot_self_zero`] at `V := CPoint.sub A B`.
fn declare_eq_zero_of_dist_sq_eq_zero(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let sub_ab = psub(d, p, pa, pb);
    let dist_ab = d.const_app(p.dist_sq, &[pa, pb]); // defeq (dot sub_ab sub_ab)
    let zero = czero(d, p);
    let hypothesis = equiv(d, p, dist_ab, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let mp_body = d.lemma(p.eq_zero_of_dot_self_zero, &[sub_ab, h]);
    // mp_body : CPoint.Equiv sub_ab zero_point

    let zp = zero_point(d, p);
    let dx = d.const_app(p.x, &[sub_ab]);
    let dy = d.const_app(p.y, &[sub_ab]);
    let zx = d.const_app(p.x, &[zp]);
    let zy = d.const_app(p.y, &[zp]);
    let ex_ty = equiv(d, p, dx, zx);
    let ey_ty = equiv(d, p, dy, zy);
    let hx = d.and_left(ex_ty, ey_ty, mp_body); // Equiv dx zx, defeq Equiv(x(sub A B)) zero
    let hy = d.and_right(ex_ty, ey_ty, mp_body); // Equiv dy zy, defeq Equiv(y(sub A B)) zero

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let ax_eq_bx = equiv_of_sub_eq_zero(d, p, ax, bx, hx); // Equiv ax bx
    let ay_eq_by = equiv_of_sub_eq_zero(d, p, ay, by, hy); // Equiv ay by

    let left_claim = equiv(d, p, ax, bx);
    let right_claim = equiv(d, p, ay, by);
    let body = and_intro(d, p, left_claim, right_claim, ax_eq_bx, ay_eq_by);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        let with_pb = d.lam_fv(pb_fv, point, with_h);
        d.lam_fv(pa_fv, point, with_pb)
    };
    let ty = {
        let claim = d.const_app(p.point_equiv, &[pa, pb]);
        let inner = d.arrow(hypothesis, claim);
        let with_pb = d.pi_fv(pb_fv, point, inner);
        d.pi_fv(pa_fv, point, with_pb)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.eq_zero_of_dist_sq_eq_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.distSq_eq_zero_iff`: the biconditional, from
/// [`declare_eq_zero_of_dist_sq_eq_zero`] (`mp`) and
/// [`declare_dist_sq_eq_zero_of_equiv`] (`mpr`) — a restatement, in the same
/// style as [`declare_dot_self_zero_iff`].
fn declare_dist_sq_eq_zero_iff(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let logic = creal.rat.int.logic;
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let zero = czero(d, p);
    let dist_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let dist_stmt = equiv(d, p, dist_ab, zero);
    let point_stmt = d.const_app(p.point_equiv, &[pa, pb]);

    // mp : Equiv (distSq A B) zero -> CPoint.Equiv A B
    let mp_body = d.lemma(p.eq_zero_of_dist_sq_eq_zero, &[pa, pb]);
    // mpr : CPoint.Equiv A B -> Equiv (distSq A B) zero
    let mpr_body = d.lemma(p.dist_sq_eq_zero_of_equiv, &[pa, pb]);

    let iff_stmt = d.const_app(logic.iff, &[dist_stmt, point_stmt]);
    let iff_proof = d.const_app(logic.iff_intro, &[dist_stmt, point_stmt, mp_body, mpr_body]);

    let value = {
        let with_pb = d.lam_fv(pb_fv, point, iff_proof);
        d.lam_fv(pa_fv, point, with_pb)
    };
    let ty = {
        let with_pb = d.pi_fv(pb_fv, point, iff_stmt);
        d.pi_fv(pa_fv, point, with_pb)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dist_sq_eq_zero_iff,
        uparams: vec![],
        ty,
        value,
    })
}

// --- perpendicular bisector: the locus of points equidistant from two ------

/// `Equiv (add m (neg v)) (neg (add m (neg u)))` — `m - v ~ -(m - u)`, given
/// `m` is literally `midpoint u v` (so `Equiv m (midpoint u v)` holds by
/// `refl`, the same idiom [`apollonius_neg_swap_scalar_proof`] uses). The
/// per-coordinate content of [`declare_perp_bisector_midpoint`]: the
/// midpoint of `u,v` is equidistant from both, because `m - v` and
/// `-(m - u)` are the same displacement.
fn midpoint_equidistant_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    u: ExprId,
    v: ExprId,
    m: ExprId,
) -> ExprId {
    let refl_m = refl(d, p, m);
    let h_double = double_o_eq_a_plus_b_proof(d, p, u, v, m, refl_m); // Equiv(m+m, u+v)
    let swap = sum_swap_proof(d, p, m, m, u, v, h_double); // Equiv(u-m, m-v)
    let neg_m = cneg(d, p, m);
    let u_negm = cadd(d, p, u, neg_m);
    let neg_v = cneg(d, p, v);
    let m_negv = cadd(d, p, m, neg_v);
    let swap_symm = symm(d, p, u_negm, m_negv, swap); // Equiv(m-v, u-m)

    let nsc = neg_sub_comm_scalar_proof(d, p, m, u); // Equiv(neg(m-u), u-m)
    let neg_u = cneg(d, p, u);
    let m_negu = cadd(d, p, m, neg_u);
    let neg_m_negu = cneg(d, p, m_negu);
    let nsc_symm = symm(d, p, neg_m_negu, u_negm, nsc); // Equiv(u-m, neg(m-u))

    chain(d, p, m_negv, &[(u_negm, swap_symm), (neg_m_negu, nsc_symm)])
}

/// `CPoint.OnPerpBisector P A B := Equiv (distSq P A) (distSq P B)`. See
/// [`CPointPrelude::on_perp_bisector`].
fn declare_on_perp_bisector(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let prop = d.kernel().sort_zero();

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);

    let dsq_pa = d.const_app(p.dist_sq, &[pp, pa]);
    let dsq_pb = d.const_app(p.dist_sq, &[pp, pb]);
    let claim = equiv(d, p, dsq_pa, dsq_pb);

    let value = {
        let inner = d.lam_fv(b_fv, point, claim);
        let mid = d.lam_fv(a_fv, point, inner);
        d.lam_fv(pp_fv, point, mid)
    };
    let ty = {
        let inner = d.arrow(point, prop);
        let mid = d.arrow(point, inner);
        d.arrow(point, mid)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.on_perp_bisector,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 15),
    })
}

/// `CPoint.OnCircle P O r2 := Equiv (distSq P O) r2`. See
/// [`CPointPrelude::on_circle`].
fn declare_on_circle(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let prop = d.kernel().sort_zero();

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let dsq_po = d.const_app(p.dist_sq, &[pp, po]);
    let claim = equiv(d, p, dsq_po, r);

    let value = {
        let inner = d.lam_fv(r_fv, carrier, claim);
        let mid = d.lam_fv(o_fv, point, inner);
        d.lam_fv(pp_fv, point, mid)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        let mid = d.arrow(point, inner);
        d.arrow(point, mid)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.on_circle,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 16),
    })
}

/// **The midpoint of a segment lies on its own perpendicular bisector.**
/// See [`CPointPrelude::perp_bisector_midpoint`].
fn declare_perp_bisector_midpoint(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);

    let mx = midpoint(d, p, ax, bx);
    let my = midpoint(d, p, ay, by);

    let x_fact = midpoint_equidistant_scalar_proof(d, p, ax, bx, mx); // Equiv(mx-bx, neg(mx-ax))
    let y_fact = midpoint_equidistant_scalar_proof(d, p, ay, by, my);

    let neg_bx = cneg(d, p, bx);
    let mx_bx = cadd(d, p, mx, neg_bx);
    let neg_ax = cneg(d, p, ax);
    let mx_ax = cadd(d, p, mx, neg_ax);
    let neg_mx_ax = cneg(d, p, mx_ax);
    let claim_x = equiv(d, p, mx_bx, neg_mx_ax);

    let neg_by = cneg(d, p, by);
    let my_by = cadd(d, p, my, neg_by);
    let neg_ay = cneg(d, p, ay);
    let my_ay = cadd(d, p, my, neg_ay);
    let neg_my_ay = cneg(d, p, my_ay);
    let claim_y = equiv(d, p, my_by, neg_my_ay);

    let point_fact = and_intro(d, p, claim_x, claim_y, x_fact, y_fact);
    // point_fact : CPoint.Equiv (sub M B) (neg (sub M A))  [defeq]

    let pm = d.const_app(p.point_midpoint, &[pa, pb]);
    let sub_mb = psub(d, p, pm, pb);
    let sub_ma = psub(d, p, pm, pa);
    let neg_sub_ma = pneg(d, p, sub_ma);

    let dot_congr_proof = d.lemma(
        p.dot_congr,
        &[
            sub_mb, neg_sub_ma, sub_mb, neg_sub_ma, point_fact, point_fact,
        ],
    );
    let dnn = dot_neg_neg_proof(d, p, sub_ma); // Equiv(dot(neg sub_ma, neg sub_ma), dot(sub_ma, sub_ma))

    let dsq_pm_pb = dotp(d, p, sub_mb, sub_mb);
    let dot_negneg = dotp(d, p, neg_sub_ma, neg_sub_ma);
    let dsq_pm_pa = dotp(d, p, sub_ma, sub_ma);

    let combined = chain(
        d,
        p,
        dsq_pm_pb,
        &[(dot_negneg, dot_congr_proof), (dsq_pm_pa, dnn)],
    );
    let final_proof = symm(d, p, dsq_pm_pb, dsq_pm_pa, combined);

    let ty_body = d.const_app(p.on_perp_bisector, &[pm, pa, pb]);
    let ty = {
        let inner = d.pi_fv(b_fv, point, ty_body);
        d.pi_fv(a_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(b_fv, point, final_proof);
        d.lam_fv(a_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.perp_bisector_midpoint,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv x CReal.zero`, given `h : Equiv (add x x) CReal.zero` — the
/// "cancel a factor of two" step [`declare_perp_bisector_iff_dot`] needs in
/// its harder direction. This kernel has no direct halving lemma, so the
/// route is to multiply both sides by `inv2` and simplify each side
/// independently: `inv2*(x+x) ~ inv2*0 ~ 0`, and separately
/// `inv2*(x+x) ~ inv2*(two*x) ~ (inv2*two)*x ~ one*x ~ x`.
fn zero_of_double_zero(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, h: ExprId) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let two = d.kernel().const_(p.two, vec![]);
    let one = d.kernel().const_(creal.one, vec![]);

    let x_x = cadd(d, p, x, x);
    let inv2_xx = cmul(d, p, inv2, x_x);

    // Route A: inv2_xx ~ zero.
    let refl_inv2 = refl(d, p, inv2);
    let congr_h = d.lemma(creal.mul_congr, &[inv2, inv2, x_x, zero, refl_inv2, h]);
    let inv2_zero = cmul(d, p, inv2, zero);
    let mz = d.lemma(creal.mul_zero, &[inv2]); // Equiv(inv2_zero, zero)
    let route_a = chain(d, p, inv2_xx, &[(inv2_zero, congr_h), (zero, mz)]);

    // Route B: inv2_xx ~ x.
    let two_x = cmul(d, p, two, x);
    let tmed = two_mul_eq_double_proof(d, p, x); // Equiv(two_x, x_x)
    let tmed_symm = symm(d, p, two_x, x_x, tmed); // Equiv(x_x, two_x)
    let congr1 = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, x_x, two_x, refl_inv2, tmed_symm],
    );
    let inv2_two_x = cmul(d, p, inv2, two_x);

    let inv2_two = cmul(d, p, inv2, two);
    let inv2_two_via_x = cmul(d, p, inv2_two, x);
    let assoc = d.lemma(creal.mul_assoc, &[inv2, two, x]); // Equiv(inv2_two_via_x, inv2_two_x)
    let assoc_symm = symm(d, p, inv2_two_via_x, inv2_two_x, assoc);

    let two_inv2 = cmul(d, p, two, inv2);
    let comm = d.lemma(creal.mul_comm, &[inv2, two]); // Equiv(inv2_two, two_inv2)
    let zero_nat = d.num(0);
    let h_two = d.kernel().const_(p.two_pos_bound, vec![]);
    let cancel = d.lemma(creal.mul_inv_cancel, &[two, zero_nat, h_two]); // Equiv(two_inv2, one)
    let inv2_two_is_one = chain(d, p, inv2_two, &[(two_inv2, comm), (one, cancel)]);

    let refl_x = refl(d, p, x);
    let congr2 = d.lemma(
        creal.mul_congr,
        &[inv2_two, one, x, x, inv2_two_is_one, refl_x],
    );
    let one_x = cmul(d, p, one, x);
    let omp = one_mul_proof(d, p, x); // Equiv(one_x, x)

    let route_b = chain(
        d,
        p,
        inv2_xx,
        &[
            (inv2_two_x, congr1),
            (inv2_two_via_x, assoc_symm),
            (one_x, congr2),
            (x, omp),
        ],
    );

    let route_b_symm = symm(d, p, inv2_xx, x, route_b); // Equiv(x, inv2_xx)
    chain(d, p, x, &[(inv2_xx, route_b_symm), (zero, route_a)])
}

/// Given opaque `CReal` terms `x, y, z`, proves
/// `Equiv (add (add x (add y (add y z))) (neg (add x (add (neg y) (add (neg y) z)))))
///        (add (add y y) (add y y))`,
/// i.e. `(x + 2y + z) - (x - 2y + z) ~ 4y` (`2X` written `X+X`) — the
/// combination step [`declare_perp_bisector_iff_dot`] needs after expanding
/// `distSq P A` via [`CPointPrelude::dot_self_add`] and `distSq P B` via
/// [`CPointPrelude::dot_self_sub`], both at `(U, V)`: `x := dot U U`,
/// `y := dot U V`, `z := dot V V`.
fn perp_bisector_combine_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ny = cneg(d, p, y);
    let ny_z = cadd(d, p, ny, z); // -y + z
    let inner1 = cadd(d, p, ny, ny_z); // -y + (-y + z)
    let term_sub = cadd(d, p, x, inner1); // x + (-y + (-y + z))

    let y_z = cadd(d, p, y, z); // y + z
    let inner2 = cadd(d, p, y, y_z); // y + (y + z)
    let term_add = cadd(d, p, x, inner2); // x + (y + (y + z))

    let neg_z = cneg(d, p, z);
    let y_negz = cadd(d, p, y, neg_z); // y + (-z)
    let inner3 = cadd(d, p, y, y_negz); // y + (y + (-z))
    let neg_x = cneg(d, p, x);
    let term_sub_neg_target = cadd(d, p, neg_x, inner3); // -x + (y + (y + (-z)))

    // neg(inner1) ~ inner3.
    let neg_inner1_reduce = {
        let na2 = neg_add_proof(d, p, ny, ny_z); // Equiv(neg inner1, neg_ny + neg_ny_z)
        let neg_ny = cneg(d, p, ny);
        let neg_ny_z = cneg(d, p, ny_z);
        let neg_ny_plus_neg_nyz = cadd(d, p, neg_ny, neg_ny_z);

        let nn1 = neg_neg_proof(d, p, y); // Equiv(neg_ny, y)
        let na3 = neg_add_proof(d, p, ny, z); // Equiv(neg_ny_z, neg_ny + neg_z)
        let neg_z2 = cneg(d, p, z);
        let neg_ny_2 = cneg(d, p, ny);
        let neg_ny_plus_negz = cadd(d, p, neg_ny_2, neg_z2);
        let refl_negz2 = refl(d, p, neg_z2);
        let congr_nnz = d.lemma(
            creal.add_congr,
            &[neg_ny_2, y, neg_z2, neg_z2, nn1, refl_negz2],
        ); // Equiv(neg_ny+neg_z, y+neg_z)
        let neg_nyz_reduce = chain(
            d,
            p,
            neg_ny_z,
            &[(neg_ny_plus_negz, na3), (y_negz, congr_nnz)],
        ); // Equiv(neg_ny_z, y_negz)

        let congr_full = d.lemma(
            creal.add_congr,
            &[neg_ny, y, neg_ny_z, y_negz, nn1, neg_nyz_reduce],
        ); // Equiv(neg_ny+neg_ny_z, y+y_negz) = Equiv(_, inner3)

        let neg_inner1_start = cneg(d, p, inner1);
        chain(
            d,
            p,
            neg_inner1_start,
            &[(neg_ny_plus_neg_nyz, na2), (inner3, congr_full)],
        )
    };

    let na1 = neg_add_proof(d, p, x, inner1); // Equiv(neg term_sub, neg_x + neg_inner1)
    let neg_inner1 = cneg(d, p, inner1);
    let neg_x_neg_inner1 = cadd(d, p, neg_x, neg_inner1);
    let refl_neg_x = refl(d, p, neg_x);
    let congr_final = d.lemma(
        creal.add_congr,
        &[
            neg_x,
            neg_x,
            neg_inner1,
            inner3,
            refl_neg_x,
            neg_inner1_reduce,
        ],
    ); // Equiv(neg_x_neg_inner1, term_sub_neg_target)
    let neg_term_sub = cneg(d, p, term_sub);
    let neg_term_sub_reduce = chain(
        d,
        p,
        neg_term_sub,
        &[(neg_x_neg_inner1, na1), (term_sub_neg_target, congr_final)],
    );

    let sum = cadd(d, p, term_add, neg_term_sub);
    let refl_term_add = refl(d, p, term_add);
    let congr_sum = d.lemma(
        creal.add_congr,
        &[
            term_add,
            term_add,
            neg_term_sub,
            term_sub_neg_target,
            refl_term_add,
            neg_term_sub_reduce,
        ],
    );
    let sum2 = cadd(d, p, term_add, term_sub_neg_target); // (x+inner2) + (neg_x+inner3)

    // Reassociate: (x+inner2)+(neg_x+inner3) ~ (x+neg_x)+(inner2+inner3).
    let swap1 = add_middle_swap_proof(d, p, x, inner2, neg_x, inner3);
    let x_negx = cadd(d, p, x, neg_x);
    let inner2_inner3 = cadd(d, p, inner2, inner3);
    let after_swap1 = cadd(d, p, x_negx, inner2_inner3);

    let an_x = d.lemma(creal.add_neg, &[x]); // Equiv(x_negx, zero)
    let zero = czero(d, p);
    let refl_i23 = refl(d, p, inner2_inner3);
    let congr_zero = d.lemma(
        creal.add_congr,
        &[x_negx, zero, inner2_inner3, inner2_inner3, an_x, refl_i23],
    );
    let zero_i23 = cadd(d, p, zero, inner2_inner3);
    let za = zero_add_proof(d, p, inner2_inner3); // Equiv(zero_i23, inner2_inner3)
    let after_cancel_x = chain(
        d,
        p,
        after_swap1,
        &[(zero_i23, congr_zero), (inner2_inner3, za)],
    );

    // inner2+inner3 = (y+(y+z))+(y+(y+(-z))) ~ (y+y) + ((y+z)+(y+(-z))) ~ (y+y)+(y+y).
    let swap2 = add_middle_swap_proof(d, p, y, y_z, y, y_negz);
    let yy = cadd(d, p, y, y);
    let yz_ynegz = cadd(d, p, y_z, y_negz);
    let after_swap2 = cadd(d, p, yy, yz_ynegz);

    let swap3 = add_middle_swap_proof(d, p, y, z, y, neg_z);
    let z_negz = cadd(d, p, z, neg_z);
    let yy_zz = cadd(d, p, yy, z_negz);
    let an_z = d.lemma(creal.add_neg, &[z]); // Equiv(z_negz, zero)
    let refl_yy = refl(d, p, yy);
    let congr_yz = d.lemma(creal.add_congr, &[yy, yy, z_negz, zero, refl_yy, an_z]);
    let yy_zero = cadd(d, p, yy, zero);
    let az_yy = d.lemma(creal.add_zero, &[yy]); // Equiv(yy_zero, yy)
    let yz_ynegz_reduce = chain(
        d,
        p,
        yz_ynegz,
        &[(yy_zz, swap3), (yy_zero, congr_yz), (yy, az_yy)],
    );

    let refl_yy2 = refl(d, p, yy);
    let congr_final2 = d.lemma(
        creal.add_congr,
        &[yy, yy, yz_ynegz, yy, refl_yy2, yz_ynegz_reduce],
    );
    let target = cadd(d, p, yy, yy);
    let inner2_inner3_reduce = chain(
        d,
        p,
        inner2_inner3,
        &[(after_swap2, swap2), (target, congr_final2)],
    );

    chain(
        d,
        p,
        sum,
        &[
            (sum2, congr_sum),
            (after_swap1, swap1),
            (inner2_inner3, after_cancel_x),
            (target, inner2_inner3_reduce),
        ],
    )
}

/// `Equiv (add (add m (neg u)) (add m (neg u))) (add v (neg u))` —
/// `(m-u)+(m-u) ~ v-u`, given `m` is literally `midpoint u v`. The
/// per-coordinate content [`declare_perp_bisector_iff_dot`] needs to relate
/// `sub B A` (the full side) to `sub (midpoint A B) A` doubled (the half
/// side).
fn half_diff_double_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    u: ExprId,
    v: ExprId,
    m: ExprId,
) -> ExprId {
    let creal = p.creal;
    let refl_m = refl(d, p, m);
    let h = double_o_eq_a_plus_b_proof(d, p, u, v, m, refl_m); // Equiv(m+m, u+v)
    let neg_u = cneg(d, p, u);
    let m_negu = cadd(d, p, m, neg_u);
    let lhs = cadd(d, p, m_negu, m_negu);

    let swap1 = add_middle_swap_proof(d, p, m, neg_u, m, neg_u); // Equiv(lhs, (m+m)+(negu+negu))
    let mm = cadd(d, p, m, m);
    let negu_negu = cadd(d, p, neg_u, neg_u);
    let mm_negu = cadd(d, p, mm, negu_negu);

    let uv = cadd(d, p, u, v);
    let refl_nn = refl(d, p, negu_negu);
    let congr1 = d.lemma(creal.add_congr, &[mm, uv, negu_negu, negu_negu, h, refl_nn]);
    let uv_negu = cadd(d, p, uv, negu_negu);

    let swap2 = add_middle_swap_proof(d, p, u, v, neg_u, neg_u); // Equiv(uv_negu, (u+negu)+(v+negu))
    let u_negu = cadd(d, p, u, neg_u);
    let v_negu = cadd(d, p, v, neg_u);
    let u_negu_v_negu = cadd(d, p, u_negu, v_negu);

    let an = d.lemma(creal.add_neg, &[u]); // Equiv(u_negu, zero)
    let zero = czero(d, p);
    let refl_vnegu = refl(d, p, v_negu);
    let congr2 = d.lemma(
        creal.add_congr,
        &[u_negu, zero, v_negu, v_negu, an, refl_vnegu],
    );
    let zero_vnegu = cadd(d, p, zero, v_negu);
    let za = zero_add_proof(d, p, v_negu); // Equiv(zero_vnegu, v_negu)

    chain(
        d,
        p,
        lhs,
        &[
            (mm_negu, swap1),
            (uv_negu, congr1),
            (u_negu_v_negu, swap2),
            (zero_vnegu, congr2),
            (v_negu, za),
        ],
    )
}

/// **The perpendicular-bisector characterisation.** See
/// [`CPointPrelude::perp_bisector_iff_dot`].
fn declare_perp_bisector_iff_dot(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let logic = creal.rat.int.logic;
    let point = point_ty(d, p);

    let p_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(p_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);

    let px = d.const_app(p.x, &[pp]);
    let py = d.const_app(p.y, &[pp]);
    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);

    let mx = midpoint(d, p, ax, bx);
    let my = midpoint(d, p, ay, by);
    let pm = d.const_app(p.point_midpoint, &[pa, pb]);

    // U := P - M, V := M - A, W := B - A (all point-level, folded `pm`).
    let big_u = psub(d, p, pp, pm);
    let big_v = psub(d, p, pm, pa);
    let big_w = psub(d, p, pb, pa);

    // fact_a: CPoint.Equiv (sub P A) (add U V).
    let neg_ax = cneg(d, p, ax);
    let neg_bx = cneg(d, p, bx);
    let neg_mx = cneg(d, p, mx);
    let neg_ay = cneg(d, p, ay);
    let neg_by = cneg(d, p, by);
    let neg_my = cneg(d, p, my);

    let px_mx = cadd(d, p, px, neg_mx);
    let mx_ax = cadd(d, p, mx, neg_ax);
    let px_ax = cadd(d, p, px, neg_ax);
    let u_plus_v_x = cadd(d, p, px_mx, mx_ax);
    let fact_a_x_ty = equiv(d, p, px_ax, u_plus_v_x);
    let fact_a_x = telescope_scalar_proof(d, p, px, mx, ax);

    let py_my = cadd(d, p, py, neg_my);
    let my_ay = cadd(d, p, my, neg_ay);
    let py_ay = cadd(d, p, py, neg_ay);
    let u_plus_v_y = cadd(d, p, py_my, my_ay);
    let fact_a_y_ty = equiv(d, p, py_ay, u_plus_v_y);
    let fact_a_y = telescope_scalar_proof(d, p, py, my, ay);

    let fact_a = and_intro(d, p, fact_a_x_ty, fact_a_y_ty, fact_a_x, fact_a_y);

    // fact_b: CPoint.Equiv (sub P B) (sub U V).
    // px-bx ~ (px-mx)+(mx-bx), then mx-bx ~ neg(mx-ax) [midpoint_equidistant].
    let px_bx = cadd(d, p, px, neg_bx);
    let mx_bx = cadd(d, p, mx, neg_bx);
    let step_x = telescope_scalar_proof(d, p, px, mx, bx); // Equiv(px-bx, (px-mx)+(mx-bx))
    let px_mx_mx_bx = cadd(d, p, px_mx, mx_bx);
    let mb_x = midpoint_equidistant_scalar_proof(d, p, ax, bx, mx); // Equiv(mx-bx, neg(mx-ax))
    let neg_mx_ax = cneg(d, p, mx_ax);
    let refl_pxmx = refl(d, p, px_mx);
    let congr_bx = d.lemma(
        creal.add_congr,
        &[px_mx, px_mx, mx_bx, neg_mx_ax, refl_pxmx, mb_x],
    ); // Equiv(px_mx_mx_bx, u_minus_v_x)
    let u_minus_v_x = cadd(d, p, px_mx, neg_mx_ax);
    let fact_b_x = chain(
        d,
        p,
        px_bx,
        &[(px_mx_mx_bx, step_x), (u_minus_v_x, congr_bx)],
    );
    let fact_b_x_ty = equiv(d, p, px_bx, u_minus_v_x);

    let py_by = cadd(d, p, py, neg_by);
    let my_by = cadd(d, p, my, neg_by);
    let step_y = telescope_scalar_proof(d, p, py, my, by);
    let py_my_my_by = cadd(d, p, py_my, my_by);
    let mb_y = midpoint_equidistant_scalar_proof(d, p, ay, by, my);
    let neg_my_ay = cneg(d, p, my_ay);
    let refl_pymy = refl(d, p, py_my);
    let congr_by = d.lemma(
        creal.add_congr,
        &[py_my, py_my, my_by, neg_my_ay, refl_pymy, mb_y],
    );
    let u_minus_v_y = cadd(d, p, py_my, neg_my_ay);
    let fact_b_y = chain(
        d,
        p,
        py_by,
        &[(py_my_my_by, step_y), (u_minus_v_y, congr_by)],
    );
    let fact_b_y_ty = equiv(d, p, py_by, u_minus_v_y);

    let fact_b = and_intro(d, p, fact_b_x_ty, fact_b_y_ty, fact_b_x, fact_b_y);

    // W ~ V + V.
    let mx_ax_mx_ax = cadd(d, p, mx_ax, mx_ax);
    let bx_ax = cadd(d, p, bx, neg_ax);
    let wfact_x = half_diff_double_proof(d, p, ax, bx, mx); // Equiv((mx-ax)+(mx-ax), bx-ax)
    let wfact_x_symm = symm(d, p, mx_ax_mx_ax, bx_ax, wfact_x);
    let my_ay_my_ay = cadd(d, p, my_ay, my_ay);
    let by_ay = cadd(d, p, by, neg_ay);
    let wfact_y = half_diff_double_proof(d, p, ay, by, my);
    let wfact_y_symm = symm(d, p, my_ay_my_ay, by_ay, wfact_y);
    let w_x_ty = equiv(d, p, bx_ax, mx_ax_mx_ax);
    let w_y_ty = equiv(d, p, by_ay, my_ay_my_ay);
    let w_fact = and_intro(d, p, w_x_ty, w_y_ty, wfact_x_symm, wfact_y_symm);
    // w_fact : CPoint.Equiv W (add V V)  [defeq]

    // distSq P A ~ dot(U+V,U+V) ~[dot_self_add] x+(y+(y+z))  [x:=dot U U, y:=dot U V, z:=dot V V]
    let sub_pa = psub(d, p, pp, pa);
    let sub_pb = psub(d, p, pp, pb);
    let u_plus_v = padd(d, p, big_u, big_v);
    let u_minus_v = psub(d, p, big_u, big_v);

    let dcongr_a = d.lemma(
        p.dot_congr,
        &[sub_pa, u_plus_v, sub_pa, u_plus_v, fact_a, fact_a],
    );
    let dsq_pa = dotp(d, p, sub_pa, sub_pa);
    let dot_upv_upv = dotp(d, p, u_plus_v, u_plus_v);
    let dsa = d.lemma(p.dot_self_add, &[big_u, big_v]); // Equiv(dot_upv_upv, x+(y+(y+z)))
    let x_ = dotp(d, p, big_u, big_u);
    let y_ = dotp(d, p, big_u, big_v);
    let z_ = dotp(d, p, big_v, big_v);
    let y_z = cadd(d, p, y_, z_);
    let y_y_z = cadd(d, p, y_, y_z);
    let term_add = cadd(d, p, x_, y_y_z);
    let dsq_pa_expand = chain(d, p, dsq_pa, &[(dot_upv_upv, dcongr_a), (term_add, dsa)]);

    let dcongr_b = d.lemma(
        p.dot_congr,
        &[sub_pb, u_minus_v, sub_pb, u_minus_v, fact_b, fact_b],
    );
    let dsq_pb = dotp(d, p, sub_pb, sub_pb);
    let dot_umv_umv = dotp(d, p, u_minus_v, u_minus_v);
    let dss = d.lemma(p.dot_self_sub, &[big_u, big_v]); // Equiv(dot_umv_umv, x+(-y+(-y+z)))
    let neg_y = cneg(d, p, y_);
    let neg_y_z = cadd(d, p, neg_y, z_);
    let neg_y_neg_y_z = cadd(d, p, neg_y, neg_y_z);
    let term_sub = cadd(d, p, x_, neg_y_neg_y_z);
    let dsq_pb_expand = chain(d, p, dsq_pb, &[(dot_umv_umv, dcongr_b), (term_sub, dss)]);

    // combine ~ (y+y)+(y+y).
    let combine = perp_bisector_combine_proof(d, p, x_, y_, z_);
    // combine : Equiv(term_add + neg(term_sub), (y+y)+(y+y))

    let neg_dsq_pb = cneg(d, p, dsq_pb);
    let neg_term_sub = cneg(d, p, term_sub);
    let neg_congr = d.lemma(creal.neg_congr, &[dsq_pb, term_sub, dsq_pb_expand]);
    let diff_ab = cadd(d, p, dsq_pa, neg_dsq_pb);
    let refl_dsqpa = refl(d, p, dsq_pa);
    let step_diff1 = d.lemma(
        creal.add_congr,
        &[
            dsq_pa,
            dsq_pa,
            neg_dsq_pb,
            neg_term_sub,
            refl_dsqpa,
            neg_congr,
        ],
    ); // Equiv(diff_ab, dsq_pa+neg_term_sub)
    let dsq_pa_neg_term_sub = cadd(d, p, dsq_pa, neg_term_sub);
    let refl_negts = refl(d, p, neg_term_sub);
    let step_diff2 = d.lemma(
        creal.add_congr,
        &[
            dsq_pa,
            term_add,
            neg_term_sub,
            neg_term_sub,
            dsq_pa_expand,
            refl_negts,
        ],
    ); // Equiv(dsq_pa+neg_term_sub, term_add+neg_term_sub)
    let term_add_neg_term_sub = cadd(d, p, term_add, neg_term_sub);
    let yy = cadd(d, p, y_, y_);
    let target = cadd(d, p, yy, yy);

    let diff_ab_expand = chain(
        d,
        p,
        diff_ab,
        &[
            (dsq_pa_neg_term_sub, step_diff1),
            (term_add_neg_term_sub, step_diff2),
            (target, combine),
        ],
    );
    // diff_ab_expand : Equiv(distSq P A - distSq P B, (y+y)+(y+y))

    // X := dot(U, W) ~ dot(U, V+V) ~ y+y.
    let big_x = dotp(d, p, big_u, big_w);
    let v_plus_v = padd(d, p, big_v, big_v);
    let refl_u = point_equiv_refl(d, p, big_u);
    let dcongr_x = d.lemma(
        p.dot_congr,
        &[big_u, big_u, big_w, v_plus_v, refl_u, w_fact],
    );
    let dot_u_vpv = dotp(d, p, big_u, v_plus_v);
    let dar = d.lemma(p.dot_add_right, &[big_u, big_v, big_v]); // Equiv(dot_u_vpv, y+y)
    let x_eq_yy = chain(d, p, big_x, &[(dot_u_vpv, dcongr_x), (yy, dar)]);
    // x_eq_yy : Equiv(X, y+y)

    // diffAB ~ X + X.
    let x_eq_yy_symm = symm(d, p, big_x, yy, x_eq_yy); // Equiv(y+y, X)
    let congr_xx = d.lemma(
        creal.add_congr,
        &[yy, big_x, yy, big_x, x_eq_yy_symm, x_eq_yy_symm],
    );
    let x_plus_x = cadd(d, p, big_x, big_x);
    let ident = chain(
        d,
        p,
        diff_ab,
        &[(target, diff_ab_expand), (x_plus_x, congr_xx)],
    );
    // ident : Equiv(distSq P A - distSq P B, X + X)

    let zero = czero(d, p);
    let on_pb_ty = d.const_app(p.on_perp_bisector, &[pp, pa, pb]);
    let dot_stmt = equiv(d, p, big_x, zero);

    // mp : OnPerpBisector P A B -> Equiv X zero.
    let mp_body = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        // h : Equiv (distSq P A) (distSq P B)
        let cpn = cancel_pos_neg(d, p, dsq_pa, dsq_pb, h); // Equiv(diff_ab, zero)
        let ident_symm = symm(d, p, diff_ab, x_plus_x, ident); // Equiv(X+X, diff_ab)
        let xx_zero = chain(d, p, x_plus_x, &[(diff_ab, ident_symm), (zero, cpn)]);
        // xx_zero : Equiv(X+X, zero)
        let body = zero_of_double_zero(d, p, big_x, xx_zero); // Equiv(X, zero)
        d.lam_fv(h_fv, on_pb_ty, body)
    };

    // mpr : Equiv X zero -> OnPerpBisector P A B.
    let mpr_body = {
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        // hx : Equiv X zero
        let congr_hx = d.lemma(creal.add_congr, &[big_x, zero, big_x, zero, hx, hx]);
        let zero_zero = cadd(d, p, zero, zero);
        let az = d.lemma(creal.add_zero, &[zero]); // Equiv(zero_zero, zero)
        let xx_zero2 = chain(d, p, x_plus_x, &[(zero_zero, congr_hx), (zero, az)]);
        let diff_ab_zero = chain(d, p, diff_ab, &[(x_plus_x, ident), (zero, xx_zero2)]);
        // diff_ab_zero : Equiv(diff_ab, zero)
        let body = equiv_of_sub_eq_zero(d, p, dsq_pa, dsq_pb, diff_ab_zero); // Equiv(dsq_pa, dsq_pb)
        d.lam_fv(hx_fv, dot_stmt, body)
    };

    let iff_stmt = d.const_app(logic.iff, &[on_pb_ty, dot_stmt]);
    let iff_proof = d.const_app(logic.iff_intro, &[on_pb_ty, dot_stmt, mp_body, mpr_body]);

    let ty = {
        let w2 = d.pi_fv(b_fv, point, iff_stmt);
        let w1 = d.pi_fv(a_fv, point, w2);
        d.pi_fv(p_fv, point, w1)
    };
    let value = {
        let w2 = d.lam_fv(b_fv, point, iff_proof);
        let w1 = d.lam_fv(a_fv, point, w2);
        d.lam_fv(p_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.perp_bisector_iff_dot,
        uparams: vec![],
        ty,
        value,
    })
}

/// **A circumcentre lies on all three perpendicular bisectors.** See
/// [`CPointPrelude::circumcentre_on_perp_bisectors`].
fn declare_circumcentre_on_perp_bisectors(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let dsq_oa = d.const_app(p.dist_sq, &[po, pa]);
    let dsq_ob = d.const_app(p.dist_sq, &[po, pb]);
    let dsq_oc = d.const_app(p.dist_sq, &[po, pc]);

    let h1_ty = equiv(d, p, dsq_oa, dsq_ob);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = equiv(d, p, dsq_ob, dsq_oc);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let h3 = d.lemma(p.circumcentre_third_distance, &[po, pa, pb, pc, h1, h2]); // Equiv(dsq_oa, dsq_oc)

    let on_ab = d.const_app(p.on_perp_bisector, &[po, pa, pb]);
    let on_bc = d.const_app(p.on_perp_bisector, &[po, pb, pc]);
    let on_ac = d.const_app(p.on_perp_bisector, &[po, pa, pc]);
    let and_bc_ac_ty = d.and(on_bc, on_ac);

    let inner = and_intro(d, p, on_bc, on_ac, h2, h3);
    let body = and_intro(d, p, on_ab, and_bc_ac_ty, h1, inner);

    let concl = d.and(on_ab, and_bc_ac_ty);
    let ty_body = {
        let inner_ty = d.arrow(h2_ty, concl);
        d.arrow(h1_ty, inner_ty)
    };
    let ty = {
        let w3 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w3);
        let w1 = d.pi_fv(a_fv, point, w2);
        d.pi_fv(o_fv, point, w1)
    };
    let value = {
        let inner_v = d.lam_fv(h2_fv, h2_ty, body);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, inner_v);
        let w3 = d.lam_fv(c_fv, point, with_h1);
        let w2 = d.lam_fv(b_fv, point, w3);
        let w1 = d.lam_fv(a_fv, point, w2);
        d.lam_fv(o_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.circumcentre_on_perp_bisectors,
        uparams: vec![],
        ty,
        value,
    })
}
/// **Elements III.31, the converse — the headline.** See
/// [`CPointPrelude::thales_converse`]. Shares [`declare_thales`]'s
/// unconditional core identity (`dot(A-P,B-P) ~ neg(distSq A O) + distSq O
/// P`, `O := point_midpoint A B`, no hypothesis needed for that much — see
/// [`declare_thales`]'s own doc) but is not derived by editing or calling
/// that function, to avoid any risk of perturbing an already-proved theorem;
/// the shared telescoping steps are duplicated here with `O` substituted
/// directly (as [`declare_apollonius_median`]'s `M` is) rather than taken as
/// a hypothesis-bound point, since nothing here needs it to vary.
fn declare_thales_converse(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let p_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(p_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let px = d.const_app(p.x, &[pp]);
    let py = d.const_app(p.y, &[pp]);
    let mx = midpoint(d, p, ax, bx);
    let my = midpoint(d, p, ay, by);
    // `O`, substituted directly (no separate hypothesis, as in
    // `declare_apollonius_median`'s `M`); folded `pm` is used only for the
    // declared type.
    let po_pt = d.const_app(p.mk, &[mx, my]);
    let pm = d.const_app(p.point_midpoint, &[pa, pb]);

    // Hypothesis: dot(A-P,B-P) ~ zero.
    let sub_ac = psub(d, p, pa, pp);
    let sub_bc = psub(d, p, pb, pp);
    let sub_ac_bc_dot = dotp(d, p, sub_ac, sub_bc);
    let zero = czero(d, p);
    let h_ty = equiv(d, p, sub_ac_bc_dot, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // pt_x := A - O, pt_y := O - P, pt_z := neg(pt_x) + pt_y, pt_w := pt_x + pt_y.
    let pt_x = psub(d, p, pa, po_pt);
    let pt_y = psub(d, p, po_pt, pp);
    let neg_pt_x = pneg(d, p, pt_x);
    let pt_z = padd(d, p, neg_pt_x, pt_y);
    let pt_w = padd(d, p, pt_x, pt_y);

    // Shared negated/compound coordinate terms.
    let n_px = cneg(d, p, px);
    let n_py = cneg(d, p, py);
    let n_mx = cneg(d, p, mx);
    let n_my = cneg(d, p, my);
    let ax_mx = cadd(d, p, ax, n_mx);
    let ay_my = cadd(d, p, ay, n_my);
    let mx_px = cadd(d, p, mx, n_px);
    let my_py = cadd(d, p, my, n_py);

    // claim1: A - P ~ (A-O) + (O-P).
    let ax_px = cadd(d, p, ax, n_px);
    let ax_mx_mx_px = cadd(d, p, ax_mx, mx_px);
    let claim1_x_ty = equiv(d, p, ax_px, ax_mx_mx_px);
    let claim1_x = telescope_scalar_proof(d, p, ax, mx, px);
    let ay_py = cadd(d, p, ay, n_py);
    let ay_my_my_py = cadd(d, p, ay_my, my_py);
    let claim1_y_ty = equiv(d, p, ay_py, ay_my_my_py);
    let claim1_y = telescope_scalar_proof(d, p, ay, my, py);
    let claim1 = and_intro(d, p, claim1_x_ty, claim1_y_ty, claim1_x, claim1_y);

    // claim2: B - P ~ neg(A-O) + (O-P). `O` is literally `midpoint A B`
    // (`mx`/`my` are built that way above), so the hypothesis
    // `telescope_neg_scalar_proof` needs is just `refl`.
    let ho_x = refl(d, p, mx);
    let ho_y = refl(d, p, my);
    let bx_px = cadd(d, p, bx, n_px);
    let neg_ax_mx = cneg(d, p, ax_mx);
    let claim2_x_rhs = cadd(d, p, neg_ax_mx, mx_px);
    let claim2_x_ty = equiv(d, p, bx_px, claim2_x_rhs);
    let claim2_x = telescope_neg_scalar_proof(d, p, ax, bx, mx, px, ho_x);
    let by_py = cadd(d, p, by, n_py);
    let neg_ay_my = cneg(d, p, ay_my);
    let claim2_y_rhs = cadd(d, p, neg_ay_my, my_py);
    let claim2_y_ty = equiv(d, p, by_py, claim2_y_rhs);
    let claim2_y = telescope_neg_scalar_proof(d, p, ay, by, my, py, ho_y);
    let claim2 = and_intro(d, p, claim2_x_ty, claim2_y_ty, claim2_x, claim2_y);

    // dot(A-P,B-P) ~ dot(W,Z).
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

    // (T1+T2)+(T3+T4) ~ T1+T4  [T3 = neg T2] -- unconditional, no hypothesis.
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

    // Unconditional so far: Equiv(dot(A-P,B-P), t1_t4), t1_t4 = neg(dot_xx) + dot_yy.
    let unconditional = chain(
        d,
        p,
        sub_ac_bc_dot,
        &[
            (dot_wz, step1),
            (t1t2_t3t4, dot_wz_expand),
            (t1_t4, cancel_middle),
        ],
    );
    let unconditional_symm = symm(d, p, sub_ac_bc_dot, t1_t4, unconditional); // Equiv(t1_t4, dot(A-P,B-P))
    let t1_t4_zero = chain(
        d,
        p,
        t1_t4,
        &[(sub_ac_bc_dot, unconditional_symm), (zero, h)],
    );
    // t1_t4_zero : Equiv(add (neg dot_xx) dot_yy, zero)

    // Rewrite to `add dot_yy (neg dot_xx) ~ zero` and read off `dot_yy ~ dot_xx`.
    let comm_t14 = d.lemma(creal.add_comm, &[t1, dot_yy]); // Equiv(t1_t4, add dot_yy t1)
    let dot_yy_t1 = cadd(d, p, dot_yy, t1);
    let comm_t14_symm = symm(d, p, t1_t4, dot_yy_t1, comm_t14); // Equiv(dot_yy_t1, t1_t4)
    let dot_yy_sub_zero = chain(
        d,
        p,
        dot_yy_t1,
        &[(t1_t4, comm_t14_symm), (zero, t1_t4_zero)],
    );
    // dot_yy_sub_zero : Equiv(add dot_yy (neg dot_xx), zero)
    let dot_yy_eq_dot_xx = equiv_of_sub_eq_zero(d, p, dot_yy, dot_xx, dot_yy_sub_zero);
    // dot_yy_eq_dot_xx : Equiv(dot_yy, dot_xx) = Equiv(distSq O P, distSq A O)

    // distSq P O ~ distSq O P ~ distSq A O.
    let dsq_po = d.const_app(p.dist_sq, &[pp, po_pt]);
    let dsq_op = d.const_app(p.dist_sq, &[po_pt, pp]);
    let dsq_ao = d.const_app(p.dist_sq, &[pa, po_pt]);
    let comm_step = d.lemma(p.dist_sq_comm, &[pp, po_pt]); // Equiv(dsq_po, dsq_op)
    let final_proof = chain(
        d,
        p,
        dsq_po,
        &[(dsq_op, comm_step), (dsq_ao, dot_yy_eq_dot_xx)],
    );

    let dsq_po_folded = d.const_app(p.dist_sq, &[pp, pm]);
    let dsq_ao_folded = d.const_app(p.dist_sq, &[pa, pm]);
    let concl = equiv(d, p, dsq_po_folded, dsq_ao_folded);
    let ty_body = d.arrow(h_ty, concl);
    let ty = {
        let w3 = d.pi_fv(p_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h_fv, h_ty, final_proof);
        let w3 = d.lam_fv(p_fv, point, inner);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.thales_converse,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `cross`: the 2x2 determinant / twice the signed area ------------------

/// The raw (unfolded) value of `cross X Y Z` given the six projected
/// coordinates, plus its four algebraic factors `u := Yx-Xx, v := Zy-Yy,
/// w := Yy-Xy, z := Zx-Yx` (so `cross X Y Z = u*v - w*z`). Returned as a
/// tuple so callers proving facts about `cross` at a *permuted* argument
/// triple can relate the new factors back to an already-computed set without
/// re-deriving the shared sub-terms (interning makes the two constructions
/// structurally identical, so this is safe to call more than once with the
/// same coordinate `ExprId`s).
fn cross_raw(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    px: ExprId,
    py: ExprId,
    qx: ExprId,
    qy: ExprId,
    rx: ExprId,
    ry: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
    let neg_px = cneg(d, p, px);
    let neg_py = cneg(d, p, py);
    let neg_qy = cneg(d, p, qy);
    let neg_qx = cneg(d, p, qx);
    let u = cadd(d, p, qx, neg_px); // Qx - Px
    let v = cadd(d, p, ry, neg_qy); // Ry - Qy
    let w = cadd(d, p, qy, neg_py); // Qy - Py
    let z = cadd(d, p, rx, neg_qx); // Rx - Qx
    let uv = cmul(d, p, u, v);
    let wz = cmul(d, p, w, z);
    let neg_wz = cneg(d, p, wz);
    let value = cadd(d, p, uv, neg_wz);
    (value, u, v, w, z)
}

/// `CPoint.cross A B C`. See [`CPointPrelude::cross`].
fn declare_cross(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

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

    let (value_body, _u, _v, _w, _z) = cross_raw(d, p, ax, ay, bx, by, cx, cy);

    let value = {
        let inner2 = d.lam_fv(c_fv, point, value_body);
        let inner1 = d.lam_fv(b_fv, point, inner2);
        d.lam_fv(a_fv, point, inner1)
    };
    let ty = {
        let inner2 = d.arrow(point, carrier);
        let inner1 = d.arrow(point, inner2);
        d.arrow(point, inner1)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cross,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 17),
    })
}

/// `Equiv (cross A A B) CReal.zero`. See [`CPointPrelude::cross_self_left`].
fn declare_cross_self_left(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let point = point_ty(d, p);

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);

    let (value_body, u, v, w, z) = cross_raw(d, p, ax, ay, ax, ay, bx, by);
    // u = ax-ax, w = ay-ay: both directly `add_neg`-zero.

    let zero = czero(d, p);
    let eq_u = d.lemma(creal.add_neg, &[ax]); // Equiv(u, zero)
    let eq_w = d.lemma(creal.add_neg, &[ay]); // Equiv(w, zero)

    let uv = cmul(d, p, u, v);
    let refl_v = refl(d, p, v);
    let congr_uv = d.lemma(creal.mul_congr, &[u, zero, v, v, eq_u, refl_v]); // Equiv(uv, mul zero v)
    let zero_v = cmul(d, p, zero, v);
    let zmv = zero_mul_proof(d, p, v); // Equiv(zero_v, zero)
    let uv_zero = chain(d, p, uv, &[(zero_v, congr_uv), (zero, zmv)]);

    let wz = cmul(d, p, w, z);
    let refl_z = refl(d, p, z);
    let congr_wz = d.lemma(creal.mul_congr, &[w, zero, z, z, eq_w, refl_z]); // Equiv(wz, mul zero z)
    let zero_z = cmul(d, p, zero, z);
    let zmz = zero_mul_proof(d, p, z); // Equiv(zero_z, zero)
    let wz_zero = chain(d, p, wz, &[(zero_z, congr_wz), (zero, zmz)]);

    let neg_wz = cneg(d, p, wz);
    let neg_zero = cneg(d, p, zero);
    let neg_congr_wz = d.lemma(creal.neg_congr, &[wz, zero, wz_zero]); // Equiv(neg_wz, neg_zero)

    let zero_neg_zero = cadd(d, p, zero, neg_zero);
    let congr_final = d.lemma(
        creal.add_congr,
        &[uv, zero, neg_wz, neg_zero, uv_zero, neg_congr_wz],
    ); // Equiv(value_body, zero_neg_zero)
    let an_zero = d.lemma(creal.add_neg, &[zero]); // Equiv(zero_neg_zero, zero)

    let proof = chain(
        d,
        p,
        value_body,
        &[(zero_neg_zero, congr_final), (zero, an_zero)],
    );

    let cross_aab = d.const_app(p.cross, &[pa, pa, pb]);
    let ty_body = equiv(d, p, cross_aab, zero);
    let ty = {
        let inner = d.pi_fv(b_fv, point, ty_body);
        d.pi_fv(a_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(b_fv, point, proof);
        d.lam_fv(a_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cross_self_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (cross A B B) CReal.zero`. See [`CPointPrelude::cross_self_right`].
fn declare_cross_self_right(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let point = point_ty(d, p);

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);

    let (value_body, u, v, w, z) = cross_raw(d, p, ax, ay, bx, by, bx, by);
    // v = by-by, z = bx-bx: both directly `add_neg`-zero.

    let zero = czero(d, p);
    let eq_v = d.lemma(creal.add_neg, &[by]); // Equiv(v, zero)
    let eq_z = d.lemma(creal.add_neg, &[bx]); // Equiv(z, zero)

    let uv = cmul(d, p, u, v);
    let refl_u = refl(d, p, u);
    let congr_uv = d.lemma(creal.mul_congr, &[u, u, v, zero, refl_u, eq_v]); // Equiv(uv, mul u zero)
    let u_zero = cmul(d, p, u, zero);
    let muz = d.lemma(creal.mul_zero, &[u]); // Equiv(u_zero, zero)
    let uv_zero = chain(d, p, uv, &[(u_zero, congr_uv), (zero, muz)]);

    let wz = cmul(d, p, w, z);
    let refl_w = refl(d, p, w);
    let congr_wz = d.lemma(creal.mul_congr, &[w, w, z, zero, refl_w, eq_z]); // Equiv(wz, mul w zero)
    let w_zero = cmul(d, p, w, zero);
    let mwz = d.lemma(creal.mul_zero, &[w]); // Equiv(w_zero, zero)
    let wz_zero = chain(d, p, wz, &[(w_zero, congr_wz), (zero, mwz)]);

    let neg_wz = cneg(d, p, wz);
    let neg_zero = cneg(d, p, zero);
    let neg_congr_wz = d.lemma(creal.neg_congr, &[wz, zero, wz_zero]); // Equiv(neg_wz, neg_zero)

    let zero_neg_zero = cadd(d, p, zero, neg_zero);
    let congr_final = d.lemma(
        creal.add_congr,
        &[uv, zero, neg_wz, neg_zero, uv_zero, neg_congr_wz],
    ); // Equiv(value_body, zero_neg_zero)
    let an_zero = d.lemma(creal.add_neg, &[zero]); // Equiv(zero_neg_zero, zero)

    let proof = chain(
        d,
        p,
        value_body,
        &[(zero_neg_zero, congr_final), (zero, an_zero)],
    );

    let cross_abb = d.const_app(p.cross, &[pa, pb, pb]);
    let ty_body = equiv(d, p, cross_abb, zero);
    let ty = {
        let inner = d.pi_fv(b_fv, point, ty_body);
        d.pi_fv(a_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(b_fv, point, proof);
        d.lam_fv(a_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cross_self_right,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The `B ↔ C` swap negates `cross`.** See
/// [`CPointPrelude::cross_swap_bc`]: `∀ A B C, Equiv (cross A C B) (neg
/// (cross A B C))`.
fn declare_cross_swap_bc(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
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

    // value1 := raw `cross A B C`; u,v,w,z its four factors.
    let (value1, u, v, w, z) = cross_raw(d, p, ax, ay, bx, by, cx, cy);
    // value2 := raw `cross A C B`; up,vp,wp,zp its four factors.
    let (value2, up, vp, wp, zp) = cross_raw(d, p, ax, ay, cx, cy, bx, by);

    // --- Step 1: relate up,vp,wp,zp back to u,v,w,z. ---
    let z_plus_u = cadd(d, p, z, u);
    let step_up = telescope_scalar_proof(d, p, cx, bx, ax); // Equiv(up, z+u) [up = cx-ax]

    let neg_v = cneg(d, p, v);
    let step_vp_inv = neg_sub_comm_scalar_proof(d, p, cy, by); // Equiv(neg v, vp) [vp = by-cy]
    let step_vp = symm(d, p, neg_v, vp, step_vp_inv); // Equiv(vp, neg v)

    let v_plus_w = cadd(d, p, v, w);
    let step_wp = telescope_scalar_proof(d, p, cy, by, ay); // Equiv(wp, v+w) [wp = cy-ay]

    let neg_z = cneg(d, p, z);
    let step_zp_inv = neg_sub_comm_scalar_proof(d, p, cx, bx); // Equiv(neg z, zp) [zp = bx-cx]
    let step_zp = symm(d, p, neg_z, zp, step_zp_inv); // Equiv(zp, neg z)

    // --- Step 2: substitute into value2 = add(mul up vp)(neg(mul wp zp)). ---
    let up_vp = cmul(d, p, up, vp);
    let zu_negv = cmul(d, p, z_plus_u, neg_v);
    let congr1 = d.lemma(
        creal.mul_congr,
        &[up, z_plus_u, vp, neg_v, step_up, step_vp],
    ); // Equiv(up_vp, zu_negv)

    let wp_zp = cmul(d, p, wp, zp);
    let vw_negz = cmul(d, p, v_plus_w, neg_z);
    let congr2 = d.lemma(
        creal.mul_congr,
        &[wp, v_plus_w, zp, neg_z, step_wp, step_zp],
    ); // Equiv(wp_zp, vw_negz)

    let neg_wp_zp = cneg(d, p, wp_zp);
    let neg_vw_negz = cneg(d, p, vw_negz);
    let neg_congr2 = d.lemma(creal.neg_congr, &[wp_zp, vw_negz, congr2]); // Equiv(neg_wp_zp, neg_vw_negz)

    let congr_outer = d.lemma(
        creal.add_congr,
        &[up_vp, zu_negv, neg_wp_zp, neg_vw_negz, congr1, neg_congr2],
    ); // Equiv(value2, stage2)
    let stage2 = cadd(d, p, zu_negv, neg_vw_negz);

    // --- Step 3: expand `zu_negv = mul (z+u) (neg v)`. ---
    let rd1 = right_distrib_proof(d, p, z, u, neg_v);
    // rd1 : Equiv(zu_negv, add(mul z neg_v)(mul u neg_v))
    let mz_negv = cmul(d, p, z, neg_v);
    let mu_negv = cmul(d, p, u, neg_v);
    let mid3 = cadd(d, p, mz_negv, mu_negv);

    let mnr_zv = mul_neg_right_proof(d, p, z, v); // Equiv(mz_negv, neg(mul z v))
    let mnr_uv = mul_neg_right_proof(d, p, u, v); // Equiv(mu_negv, neg(mul u v))
    let mul_zv = cmul(d, p, z, v);
    let mul_uv = cmul(d, p, u, v);
    let neg_zv = cneg(d, p, mul_zv);
    let neg_uv = cneg(d, p, mul_uv);
    let congr3 = d.lemma(
        creal.add_congr,
        &[mz_negv, neg_zv, mu_negv, neg_uv, mnr_zv, mnr_uv],
    ); // Equiv(mid3, target3)
    let target3 = cadd(d, p, neg_zv, neg_uv);
    let zu_negv_reduce = chain(d, p, zu_negv, &[(mid3, rd1), (target3, congr3)]);
    // zu_negv_reduce : Equiv(zu_negv, target3)

    // --- Step 4: expand `vw_negz = mul (v+w) (neg z)`. ---
    let rd2 = right_distrib_proof(d, p, v, w, neg_z);
    let mv_negz = cmul(d, p, v, neg_z);
    let mw_negz = cmul(d, p, w, neg_z);
    let mid4 = cadd(d, p, mv_negz, mw_negz);

    let mnr_vz = mul_neg_right_proof(d, p, v, z); // Equiv(mv_negz, neg(mul v z))
    let mnr_wz = mul_neg_right_proof(d, p, w, z); // Equiv(mw_negz, neg(mul w z))
    let mul_vz = cmul(d, p, v, z);
    let mul_wz = cmul(d, p, w, z);
    let neg_vz = cneg(d, p, mul_vz);
    let neg_wz = cneg(d, p, mul_wz);
    let congr4 = d.lemma(
        creal.add_congr,
        &[mv_negz, neg_vz, mw_negz, neg_wz, mnr_vz, mnr_wz],
    ); // Equiv(mid4, target4)
    let target4 = cadd(d, p, neg_vz, neg_wz);
    let vw_negz_reduce = chain(d, p, vw_negz, &[(mid4, rd2), (target4, congr4)]);
    // vw_negz_reduce : Equiv(vw_negz, target4)

    let neg_target4 = cneg(d, p, target4);
    let neg_congr4 = d.lemma(creal.neg_congr, &[vw_negz, target4, vw_negz_reduce]);
    // neg_congr4 : Equiv(neg_vw_negz, neg_target4)

    let na4 = neg_add_proof(d, p, neg_vz, neg_wz);
    // na4 : Equiv(neg_target4, add(neg neg_vz)(neg neg_wz))
    let neg_neg_vz = cneg(d, p, neg_vz);
    let neg_neg_wz = cneg(d, p, neg_wz);
    let mid4b = cadd(d, p, neg_neg_vz, neg_neg_wz);

    let nn_vz = neg_neg_proof(d, p, mul_vz); // Equiv(neg_neg_vz, mul_vz)
    let nn_wz = neg_neg_proof(d, p, mul_wz); // Equiv(neg_neg_wz, mul_wz)
    let target4b = cadd(d, p, mul_vz, mul_wz);
    let congr4b = d.lemma(
        creal.add_congr,
        &[neg_neg_vz, mul_vz, neg_neg_wz, mul_wz, nn_vz, nn_wz],
    ); // Equiv(mid4b, target4b)

    let neg_vw_negz_reduce = chain(
        d,
        p,
        neg_vw_negz,
        &[(neg_target4, neg_congr4), (mid4b, na4), (target4b, congr4b)],
    );
    // neg_vw_negz_reduce : Equiv(neg_vw_negz, target4b)

    // --- Step 5: assemble `stage2 ~ add(target3)(target4b)` and cancel the
    // shared cross term (mul v z ~ mul z v) via `add_middle_swap_proof`. ---
    let congr_stage2 = d.lemma(
        creal.add_congr,
        &[
            zu_negv,
            target3,
            neg_vw_negz,
            target4b,
            zu_negv_reduce,
            neg_vw_negz_reduce,
        ],
    ); // Equiv(stage2, stage3)
    let stage3 = cadd(d, p, target3, target4b);

    let comm_zv = d.lemma(creal.mul_comm, &[z, v]); // Equiv(mul_zv, mul_vz)
    let neg_mul_vz = cneg(d, p, mul_vz);
    let neg_congr_zv = d.lemma(creal.neg_congr, &[mul_zv, mul_vz, comm_zv]); // Equiv(neg_zv, neg_mul_vz)
    let refl_neg_uv = refl(d, p, neg_uv);
    let congr_target3 = d.lemma(
        creal.add_congr,
        &[
            neg_zv,
            neg_mul_vz,
            neg_uv,
            neg_uv,
            neg_congr_zv,
            refl_neg_uv,
        ],
    ); // Equiv(target3, target3b)
    let target3b = cadd(d, p, neg_mul_vz, neg_uv);
    let refl_target4b = refl(d, p, target4b);
    let congr_stage3 = d.lemma(
        creal.add_congr,
        &[
            target3,
            target3b,
            target4b,
            target4b,
            congr_target3,
            refl_target4b,
        ],
    ); // Equiv(stage3, stage4)
    let stage4 = cadd(d, p, target3b, target4b);

    // (A1+A2)+(A3+A4) ~ (A1+A3)+(A2+A4), A1=neg_mul_vz,A2=neg_uv,A3=mul_vz,A4=mul_wz.
    let swap = add_middle_swap_proof(d, p, neg_mul_vz, neg_uv, mul_vz, mul_wz);
    let a1_a3 = cadd(d, p, neg_mul_vz, mul_vz);
    let a2_a4 = cadd(d, p, neg_uv, mul_wz);
    let stage5 = cadd(d, p, a1_a3, a2_a4);

    let cancel = neg_add_cancel_proof(d, p, mul_vz); // Equiv(a1_a3, zero)
    let zero = czero(d, p);
    let refl_a2_a4 = refl(d, p, a2_a4);
    let congr_stage5 = d.lemma(
        creal.add_congr,
        &[a1_a3, zero, a2_a4, a2_a4, cancel, refl_a2_a4],
    ); // Equiv(stage5, zero_a2a4)
    let zero_a2a4 = cadd(d, p, zero, a2_a4);
    let za = zero_add_proof(d, p, a2_a4); // Equiv(zero_a2a4, a2_a4)

    let value2_reduce = chain(
        d,
        p,
        value2,
        &[
            (stage2, congr_outer),
            (stage3, congr_stage2),
            (stage4, congr_stage3),
            (stage5, swap),
            (zero_a2a4, congr_stage5),
            (a2_a4, za),
        ],
    );
    // value2_reduce : Equiv(value2, a2_a4), a2_a4 = add(neg(mul u v))(mul w z)

    // --- Now show `neg(value1) ~ a2_a4` too, so `value2 ~ neg(value1)`. ---
    // value1 = add(mul_uv, neg_wz) exactly, by construction of `cross_raw`.
    let neg_value1 = cneg(d, p, value1);
    let na_v1 = neg_add_proof(d, p, mul_uv, neg_wz);
    // na_v1 : Equiv(neg_value1, add(neg mul_uv)(neg neg_wz))
    let neg_neg_wz_via_step4 = cneg(d, p, neg_wz); // == neg_neg_wz from step 4
    let add_neguv_negnegwz = cadd(d, p, neg_uv, neg_neg_wz_via_step4);
    let refl_neg_uv2 = refl(d, p, neg_uv);
    let congr_nv1 = d.lemma(
        creal.add_congr,
        &[
            neg_uv,
            neg_uv,
            neg_neg_wz_via_step4,
            mul_wz,
            refl_neg_uv2,
            nn_wz,
        ],
    ); // Equiv(add_neguv_negnegwz, a2_a4)

    let neg_value1_reduce = chain(
        d,
        p,
        neg_value1,
        &[(add_neguv_negnegwz, na_v1), (a2_a4, congr_nv1)],
    );
    // neg_value1_reduce : Equiv(neg_value1, a2_a4)
    let neg_value1_reduce_symm = symm(d, p, neg_value1, a2_a4, neg_value1_reduce);
    // Equiv(a2_a4, neg_value1)

    let final_proof = chain(
        d,
        p,
        value2,
        &[(a2_a4, value2_reduce), (neg_value1, neg_value1_reduce_symm)],
    );
    // final_proof : Equiv(value2, neg_value1) = Equiv(cross A C B, neg(cross A B C))

    let cross_acb = d.const_app(p.cross, &[pa, pc, pb]);
    let cross_abc = d.const_app(p.cross, &[pa, pb, pc]);
    let neg_cross_abc = cneg(d, p, cross_abc);
    let ty_body = equiv(d, p, cross_acb, neg_cross_abc);

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
        name: p.cross_swap_bc,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.NonCollinear A B C k := CReal.PosBound (mul (cross A B C) (cross
/// A B C)) k`. See [`CPointPrelude::non_collinear`].
fn declare_non_collinear(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let k_fv = d.fresh_fvar();
    let pk = d.kernel().fvar(k_fv);

    let cross_abc = d.const_app(p.cross, &[pa, pb, pc]);
    let cross_sq = cmul(d, p, cross_abc, cross_abc);
    let claim = d.const_app(p.creal.pos_bound, &[cross_sq, pk]);

    let value = {
        let w3 = d.lam_fv(k_fv, nat, claim);
        let w2 = d.lam_fv(c_fv, point, w3);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    let ty = {
        let w3 = d.arrow(nat, prop);
        let w2 = d.arrow(point, w3);
        let w1 = d.arrow(point, w2);
        d.arrow(point, w1)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.non_collinear,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 18),
    })
}

// --- circumcentre_unique: helpers ------------------------------------------

/// `Equiv x (neg y)`, given `h : Equiv (add x y) CReal.zero` — "if two things
/// sum to zero, each is the negation of the other." The single-value cousin
/// of [`sub_eq_zero_of_equiv`]/[`equiv_of_sub_eq_zero`]: those relate `x ~ y`
/// to `x − y ~ 0`; this relates `x + y ~ 0` to `x ~ −y`, the shape the
/// elimination steps below actually produce (raw sums, not differences).
fn neg_of_add_zero_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let xy = cadd(d, p, x, y);
    let neg_y = cneg(d, p, y);
    let ascr = add_sub_cancel_right(d, p, x, y); // Equiv(add xy neg_y, x)
    let xy_negy = cadd(d, p, xy, neg_y);
    let ascr_symm = symm(d, p, xy_negy, x, ascr); // Equiv(x, xy_negy)
    let zero = czero(d, p);
    let refl_negy = refl(d, p, neg_y);
    let congr1 = d.lemma(creal.add_congr, &[xy, zero, neg_y, neg_y, h, refl_negy]);
    let zero_negy = cadd(d, p, zero, neg_y);
    let za = zero_add_proof(d, p, neg_y); // Equiv(zero_negy, neg_y)
    chain(
        d,
        p,
        x,
        &[(xy_negy, ascr_symm), (zero_negy, congr1), (neg_y, za)],
    )
}

/// `Equiv (mul (mul t a) b) (mul (mul t b) a)` — `(t·a)·b ~ (t·b)·a`, pure
/// `mul_assoc`/`mul_comm`. Both halves of
/// [`declare_cross_annihilates_difference`]'s 2×2 elimination use this to
/// recognise a term produced by multiplying one hypothesis by `a` as the
/// same term produced by multiplying the other by `b`.
fn mul_swap_inner_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    t: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ta = cmul(d, p, t, a);
    let ta_b = cmul(d, p, ta, b);
    let ab = cmul(d, p, a, b);
    let t_ab = cmul(d, p, t, ab);
    let assoc1 = d.lemma(creal.mul_assoc, &[t, a, b]); // Equiv(ta_b, t_ab)
    let ba = cmul(d, p, b, a);
    let t_ba = cmul(d, p, t, ba);
    let comm_ab = d.lemma(creal.mul_comm, &[a, b]); // Equiv(ab, ba)
    let refl_t = refl(d, p, t);
    let congr1 = d.lemma(creal.mul_congr, &[t, t, ab, ba, refl_t, comm_ab]); // Equiv(t_ab, t_ba)
    let tb = cmul(d, p, t, b);
    let tb_a = cmul(d, p, tb, a);
    let assoc2 = d.lemma(creal.mul_assoc, &[t, b, a]); // Equiv(tb_a, t_ba)
    let assoc2_symm = symm(d, p, tb_a, t_ba, assoc2); // Equiv(t_ba, tb_a)
    chain(
        d,
        p,
        ta_b,
        &[(t_ab, assoc1), (t_ba, congr1), (tb_a, assoc2_symm)],
    )
}

/// Given `hab : Equiv (add a b) CReal.zero`, `hcd : Equiv (add c dd)
/// CReal.zero` and `hbd : Equiv b dd`, proves `Equiv a c` — "subtract two
/// zero-sums that share an addend (up to `hbd`); the other addends agree."
/// The generic step both halves of
/// [`declare_cross_annihilates_difference`]'s elimination are built from.
fn elim_step_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
    hab: ExprId,
    hcd: ExprId,
    hbd: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ha = neg_of_add_zero_proof(d, p, a, b, hab); // Equiv(a, neg b)
    let hc = neg_of_add_zero_proof(d, p, c, dd, hcd); // Equiv(c, neg dd)
    let neg_b = cneg(d, p, b);
    let neg_d = cneg(d, p, dd);
    let hbd_neg = d.lemma(creal.neg_congr, &[b, dd, hbd]); // Equiv(neg b, neg dd)
    let hc_symm = symm(d, p, c, neg_d, hc); // Equiv(neg dd, c)
    chain(d, p, a, &[(neg_b, ha), (neg_d, hbd_neg), (c, hc_symm)])
}

/// Given `h_vd : Equiv (mul v big_d) CReal.zero` and `hpb : PosBound (mul
/// big_d big_d) k` (consumed directly at its unfolded `Equiv`-of-`inv` type,
/// the way [`declare_perp_bisector_iff_dot`] consumes an `OnPerpBisector`
/// hypothesis directly), proves `Equiv v CReal.zero`. Multiply the
/// hypothesis by `big_d` (`v·(D·D) ~ 0`), then by `CReal.inv (mul big_d
/// big_d) k hpb` (`mul_inv_cancel` cancels `D·D`, `mul_one` finishes) —
/// [`declare_circumcentre_unique`]'s only route from "annihilated by the
/// determinant" to "is zero", used once per coordinate of `sub O O'`.
fn cancel_via_pos_bound_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    v: ExprId,
    big_d: ExprId,
    k: ExprId,
    hpb: ExprId,
    h_vd: ExprId,
) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let one = d.kernel().const_(creal.one, vec![]);
    let dd = cmul(d, p, big_d, big_d);
    let inv_dd = d.const_app(creal.inv, &[dd, k, hpb]);
    let cancel_dd = d.lemma(creal.mul_inv_cancel, &[dd, k, hpb]); // Equiv(mul dd inv_dd, one)

    // Step 1: (v*D)*D ~ zero.
    let vd = cmul(d, p, v, big_d);
    let vd_d = cmul(d, p, vd, big_d);
    let zero_d = cmul(d, p, zero, big_d);
    let refl_d = refl(d, p, big_d);
    let congr1 = d.lemma(creal.mul_congr, &[vd, zero, big_d, big_d, h_vd, refl_d]);
    let zmd = zero_mul_proof(d, p, big_d);
    let step1 = chain(d, p, vd_d, &[(zero_d, congr1), (zero, zmd)]); // Equiv(vd_d, zero)

    // Step 2: v*(D*D) ~ zero.
    let v_dd = cmul(d, p, v, dd);
    let assoc1 = d.lemma(creal.mul_assoc, &[v, big_d, big_d]); // Equiv(vd_d, v_dd)
    let assoc1_symm = symm(d, p, vd_d, v_dd, assoc1);
    let step2 = chain(d, p, v_dd, &[(vd_d, assoc1_symm), (zero, step1)]); // Equiv(v_dd, zero)

    // Step 3: (v*(D*D))*inv_dd ~ zero.
    let vdd_invdd = cmul(d, p, v_dd, inv_dd);
    let zero_invdd = cmul(d, p, zero, inv_dd);
    let refl_invdd = refl(d, p, inv_dd);
    let congr3 = d.lemma(
        creal.mul_congr,
        &[v_dd, zero, inv_dd, inv_dd, step2, refl_invdd],
    );
    let zmi = zero_mul_proof(d, p, inv_dd);
    let step3 = chain(d, p, vdd_invdd, &[(zero_invdd, congr3), (zero, zmi)]); // Equiv(vdd_invdd, zero)

    // Step 4: v*(dd*inv_dd) ~ zero.
    let dd_invdd = cmul(d, p, dd, inv_dd);
    let v_dd_invdd = cmul(d, p, v, dd_invdd);
    let assoc2 = d.lemma(creal.mul_assoc, &[v, dd, inv_dd]); // Equiv(vdd_invdd, v_dd_invdd)
    let assoc2_symm = symm(d, p, vdd_invdd, v_dd_invdd, assoc2);
    let step4 = chain(d, p, v_dd_invdd, &[(vdd_invdd, assoc2_symm), (zero, step3)]); // Equiv(v_dd_invdd, zero)

    // Step 5: v*one ~ zero, via mul_inv_cancel.
    let v_one = cmul(d, p, v, one);
    let refl_v = refl(d, p, v);
    let congr5 = d.lemma(creal.mul_congr, &[v, v, dd_invdd, one, refl_v, cancel_dd]); // Equiv(v_dd_invdd, v_one)
    let congr5_symm = symm(d, p, v_dd_invdd, v_one, congr5);
    let step5 = chain(d, p, v_one, &[(v_dd_invdd, congr5_symm), (zero, step4)]); // Equiv(v_one, zero)

    // Step 6: v ~ v*one ~ zero.
    let mo = d.lemma(creal.mul_one, &[v]); // Equiv(v_one, v)
    let mo_symm = symm(d, p, v_one, v, mo); // Equiv(v, v_one)
    chain(d, p, v, &[(v_one, mo_symm), (zero, step5)])
}

/// Given `h_o : Equiv (dot (sub po m) w) CReal.zero` and `h_op : Equiv (dot
/// (sub pop m) w) CReal.zero`, proves `Equiv (dot (sub po pop) w)
/// CReal.zero` — "two points both orthogonal (relative to `m`) to `w` have a
/// difference orthogonal to `w` too." [`declare_circumcentre_difference_dots`]
/// applies this once per side, at `m := point_midpoint A B`/`w := sub B A`
/// and `m := point_midpoint B C`/`w := sub C B`.
fn circumcentre_dot_diff_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    po: ExprId,
    pop: ExprId,
    m: ExprId,
    w: ExprId,
    h_o: ExprId,
    h_op: ExprId,
) -> ExprId {
    let zero = czero(d, p);

    let dsl_o = d.lemma(p.dot_sub_left, &[po, m, w]); // Equiv(dot(sub po m) w, add(dot po w)(neg(dot m w)))
    let sub_po_m = psub(d, p, po, m);
    let dot_po_m_w = dotp(d, p, sub_po_m, w);
    let dot_po_w = dotp(d, p, po, w);
    let dot_m_w = dotp(d, p, m, w);
    let neg_dot_m_w = cneg(d, p, dot_m_w);
    let rhs_o = cadd(d, p, dot_po_w, neg_dot_m_w);
    let dsl_o_symm = symm(d, p, dot_po_m_w, rhs_o, dsl_o);
    let eq_a = chain(d, p, rhs_o, &[(dot_po_m_w, dsl_o_symm), (zero, h_o)]); // Equiv(rhs_o, zero)

    let dsl_op = d.lemma(p.dot_sub_left, &[pop, m, w]);
    let sub_pop_m = psub(d, p, pop, m);
    let dot_pop_m_w = dotp(d, p, sub_pop_m, w);
    let dot_pop_w = dotp(d, p, pop, w);
    let rhs_op = cadd(d, p, dot_pop_w, neg_dot_m_w);
    let dsl_op_symm = symm(d, p, dot_pop_m_w, rhs_op, dsl_op);
    let eq_b = chain(d, p, rhs_op, &[(dot_pop_m_w, dsl_op_symm), (zero, h_op)]); // Equiv(rhs_op, zero)

    let hxz = equiv_of_sub_eq_zero(d, p, dot_po_w, dot_m_w, eq_a); // Equiv(dot_po_w, dot_m_w)
    let hyz = equiv_of_sub_eq_zero(d, p, dot_pop_w, dot_m_w, eq_b); // Equiv(dot_pop_w, dot_m_w)
    let hyz_symm = symm(d, p, dot_pop_w, dot_m_w, hyz); // Equiv(dot_m_w, dot_pop_w)
    let hxy = chain(d, p, dot_po_w, &[(dot_m_w, hxz), (dot_pop_w, hyz_symm)]); // Equiv(dot_po_w, dot_pop_w)
    let sez = sub_eq_zero_of_equiv(d, p, dot_po_w, dot_pop_w, hxy); // Equiv(add dot_po_w (neg dot_pop_w), zero)

    let dsl_diff = d.lemma(p.dot_sub_left, &[po, pop, w]); // Equiv(dot(sub po pop) w, add(dot po w)(neg(dot pop w)))
    let sub_po_pop = psub(d, p, po, pop);
    let dot_diff = dotp(d, p, sub_po_pop, w);
    let neg_dot_pop_w = cneg(d, p, dot_pop_w);
    let rhs_diff = cadd(d, p, dot_po_w, neg_dot_pop_w);
    chain(d, p, dot_diff, &[(rhs_diff, dsl_diff), (zero, sez)])
}

/// **Two circumcentres' difference is orthogonal to every side.** See
/// [`CPointPrelude::circumcentre_difference_dots`].
fn declare_circumcentre_difference_dots(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let logic = p.creal.rat.int.logic;

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let op_fv = d.fresh_fvar();
    let pop = d.kernel().fvar(op_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let dsq_oa = d.const_app(p.dist_sq, &[po, pa]);
    let dsq_ob = d.const_app(p.dist_sq, &[po, pb]);
    let dsq_oc = d.const_app(p.dist_sq, &[po, pc]);
    let dsq_opa = d.const_app(p.dist_sq, &[pop, pa]);
    let dsq_opb = d.const_app(p.dist_sq, &[pop, pb]);
    let dsq_opc = d.const_app(p.dist_sq, &[pop, pc]);

    let h1_ty = equiv(d, p, dsq_oa, dsq_ob);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = equiv(d, p, dsq_ob, dsq_oc);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h1p_ty = equiv(d, p, dsq_opa, dsq_opb);
    let h1p_fv = d.fresh_fvar();
    let h1p = d.kernel().fvar(h1p_fv);
    let h2p_ty = equiv(d, p, dsq_opb, dsq_opc);
    let h2p_fv = d.fresh_fvar();
    let h2p = d.kernel().fvar(h2p_fv);

    let cop_o = d.lemma(p.circumcentre_on_perp_bisectors, &[po, pa, pb, pc, h1, h2]);
    let cop_op = d.lemma(
        p.circumcentre_on_perp_bisectors,
        &[pop, pa, pb, pc, h1p, h2p],
    );

    let on_o_ab = d.const_app(p.on_perp_bisector, &[po, pa, pb]);
    let on_o_bc = d.const_app(p.on_perp_bisector, &[po, pb, pc]);
    let on_o_ac = d.const_app(p.on_perp_bisector, &[po, pa, pc]);
    let and_o_bc_ac = d.and(on_o_bc, on_o_ac);
    let h_o_ab = d.and_left(on_o_ab, and_o_bc_ac, cop_o);
    let rest_o = d.and_right(on_o_ab, and_o_bc_ac, cop_o);
    let h_o_bc = d.and_left(on_o_bc, on_o_ac, rest_o);

    let on_op_ab = d.const_app(p.on_perp_bisector, &[pop, pa, pb]);
    let on_op_bc = d.const_app(p.on_perp_bisector, &[pop, pb, pc]);
    let on_op_ac = d.const_app(p.on_perp_bisector, &[pop, pa, pc]);
    let and_op_bc_ac = d.and(on_op_bc, on_op_ac);
    let h_op_ab = d.and_left(on_op_ab, and_op_bc_ac, cop_op);
    let rest_op = d.and_right(on_op_ab, and_op_bc_ac, cop_op);
    let h_op_bc = d.and_left(on_op_bc, on_op_ac, rest_op);

    let zero = czero(d, p);
    let m_ab = d.const_app(p.point_midpoint, &[pa, pb]);
    let sub_ba = psub(d, p, pb, pa);
    let m_bc = d.const_app(p.point_midpoint, &[pb, pc]);
    let sub_cb = psub(d, p, pc, pb);

    let sub_o_mab = psub(d, p, po, m_ab);
    let dot_o_ab_raw = dotp(d, p, sub_o_mab, sub_ba);
    let dot_o_ab_stmt = equiv(d, p, dot_o_ab_raw, zero);
    let iff_o_ab = d.lemma(p.perp_bisector_iff_dot, &[po, pa, pb]);
    let mp_o_ab = d.const_app(logic.iff_mp, &[on_o_ab, dot_o_ab_stmt, iff_o_ab]);
    let h_o_ab_dot = d.apply(mp_o_ab, &[h_o_ab]);

    let sub_op_mab = psub(d, p, pop, m_ab);
    let dot_op_ab_raw = dotp(d, p, sub_op_mab, sub_ba);
    let dot_op_ab_stmt = equiv(d, p, dot_op_ab_raw, zero);
    let iff_op_ab = d.lemma(p.perp_bisector_iff_dot, &[pop, pa, pb]);
    let mp_op_ab = d.const_app(logic.iff_mp, &[on_op_ab, dot_op_ab_stmt, iff_op_ab]);
    let h_op_ab_dot = d.apply(mp_op_ab, &[h_op_ab]);

    let sub_o_mbc = psub(d, p, po, m_bc);
    let dot_o_bc_raw = dotp(d, p, sub_o_mbc, sub_cb);
    let dot_o_bc_stmt = equiv(d, p, dot_o_bc_raw, zero);
    let iff_o_bc = d.lemma(p.perp_bisector_iff_dot, &[po, pb, pc]);
    let mp_o_bc = d.const_app(logic.iff_mp, &[on_o_bc, dot_o_bc_stmt, iff_o_bc]);
    let h_o_bc_dot = d.apply(mp_o_bc, &[h_o_bc]);

    let sub_op_mbc = psub(d, p, pop, m_bc);
    let dot_op_bc_raw = dotp(d, p, sub_op_mbc, sub_cb);
    let dot_op_bc_stmt = equiv(d, p, dot_op_bc_raw, zero);
    let iff_op_bc = d.lemma(p.perp_bisector_iff_dot, &[pop, pb, pc]);
    let mp_op_bc = d.const_app(logic.iff_mp, &[on_op_bc, dot_op_bc_stmt, iff_op_bc]);
    let h_op_bc_dot = d.apply(mp_op_bc, &[h_op_bc]);

    let result_ab =
        circumcentre_dot_diff_proof(d, p, po, pop, m_ab, sub_ba, h_o_ab_dot, h_op_ab_dot);
    let result_bc =
        circumcentre_dot_diff_proof(d, p, po, pop, m_bc, sub_cb, h_o_bc_dot, h_op_bc_dot);

    let sub_oop = psub(d, p, po, pop);
    let dot_oop_ba = dotp(d, p, sub_oop, sub_ba);
    let concl_ab_ty = equiv(d, p, dot_oop_ba, zero);
    let dot_oop_cb = dotp(d, p, sub_oop, sub_cb);
    let concl_bc_ty = equiv(d, p, dot_oop_cb, zero);
    let body = and_intro(d, p, concl_ab_ty, concl_bc_ty, result_ab, result_bc);
    let concl = d.and(concl_ab_ty, concl_bc_ty);

    let ty_body = {
        let inner3 = d.arrow(h2p_ty, concl);
        let inner2 = d.arrow(h1p_ty, inner3);
        let inner1 = d.arrow(h2_ty, inner2);
        d.arrow(h1_ty, inner1)
    };
    let ty = {
        let w5 = d.pi_fv(c_fv, point, ty_body);
        let w4 = d.pi_fv(b_fv, point, w5);
        let w3 = d.pi_fv(a_fv, point, w4);
        let w2 = d.pi_fv(op_fv, point, w3);
        d.pi_fv(o_fv, point, w2)
    };
    let value = {
        let inner3 = d.lam_fv(h2p_fv, h2p_ty, body);
        let inner2 = d.lam_fv(h1p_fv, h1p_ty, inner3);
        let inner1 = d.lam_fv(h2_fv, h2_ty, inner2);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, inner1);
        let w5 = d.lam_fv(c_fv, point, with_h1);
        let w4 = d.lam_fv(b_fv, point, w5);
        let w3 = d.lam_fv(a_fv, point, w4);
        let w2 = d.lam_fv(op_fv, point, w3);
        d.lam_fv(o_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.circumcentre_difference_dots,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (add (add (mul vx bx) (mul vy by)) (neg (add (mul vx ax) (mul vy
/// ay)))) (add (mul vx diff_x) (mul vy diff_y))`, `diff_x := add bx (neg
/// ax)`, `diff_y := add by (neg ay)` — `(vx·bx+vy·by) − (vx·ax+vy·ay) ~
/// vx·(bx−ax) + vy·(by−ay)`, the "distribute the subtraction, then factor
/// `vx`/`vy` back out" regrouping [`declare_cross_annihilates_difference`]
/// needs to turn `dot V B − dot V A` into the raw `cross_raw`-shaped
/// factors. Returns `diff_x`/`diff_y` too so the caller reuses the exact
/// terms (rather than reconstructing structurally-identical copies) when
/// assembling `cross A B C`'s own `u`/`v`/`w`/`z`.
fn regroup_dot_diff_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    vx: ExprId,
    vy: ExprId,
    bx: ExprId,
    by: ExprId,
    ax: ExprId,
    ay: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let creal = p.creal;
    let vxbx = cmul(d, p, vx, bx);
    let vyby = cmul(d, p, vy, by);
    let vxax = cmul(d, p, vx, ax);
    let vyay = cmul(d, p, vy, ay);
    let sum_b = cadd(d, p, vxbx, vyby);
    let sum_a = cadd(d, p, vxax, vyay);
    let neg_sum_a = cneg(d, p, sum_a);
    let lhs = cadd(d, p, sum_b, neg_sum_a);

    let na = neg_add_proof(d, p, vxax, vyay); // Equiv(neg_sum_a, add(neg vxax)(neg vyay))
    let neg_vxax = cneg(d, p, vxax);
    let neg_vyay = cneg(d, p, vyay);
    let split_a = cadd(d, p, neg_vxax, neg_vyay);
    let refl_sum_b = refl(d, p, sum_b);
    let congr1 = d.lemma(
        creal.add_congr,
        &[sum_b, sum_b, neg_sum_a, split_a, refl_sum_b, na],
    );
    let mid1 = cadd(d, p, sum_b, split_a);

    let swap = add_middle_swap_proof(d, p, vxbx, vyby, neg_vxax, neg_vyay);
    let group_x = cadd(d, p, vxbx, neg_vxax);
    let group_y = cadd(d, p, vyby, neg_vyay);
    let mid2 = cadd(d, p, group_x, group_y);

    let neg_ax = cneg(d, p, ax);
    let neg_ay = cneg(d, p, ay);
    let diff_x = cadd(d, p, bx, neg_ax);
    let diff_y = cadd(d, p, by, neg_ay);
    let msr_x = mul_sub_right_proof(d, p, vx, bx, ax); // Equiv(mul vx diff_x, group_x)
    let msr_y = mul_sub_right_proof(d, p, vy, by, ay);
    let target_x = cmul(d, p, vx, diff_x);
    let target_y = cmul(d, p, vy, diff_y);
    let msr_x_symm = symm(d, p, target_x, group_x, msr_x);
    let msr_y_symm = symm(d, p, target_y, group_y, msr_y);
    let congr3 = d.lemma(
        creal.add_congr,
        &[group_x, target_x, group_y, target_y, msr_x_symm, msr_y_symm],
    );
    let target = cadd(d, p, target_x, target_y);

    let proof = chain(d, p, lhs, &[(mid1, congr1), (mid2, swap), (target, congr3)]);
    (proof, diff_x, diff_y)
}

/// **The 2×2 elimination.** See
/// [`CPointPrelude::cross_annihilates_difference`].
fn declare_cross_annihilates_difference(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let point = point_ty(d, p);

    let v_fv = d.fresh_fvar();
    let pv = d.kernel().fvar(v_fv);
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
    let vx = d.const_app(p.x, &[pv]);
    let vy = d.const_app(p.y, &[pv]);

    let zero = czero(d, p);

    let sub_ba = psub(d, p, pb, pa);
    let sub_cb = psub(d, p, pc, pb);
    let dot_v_ba_stmt = dotp(d, p, pv, sub_ba);
    let h1_ty = equiv(d, p, dot_v_ba_stmt, zero);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let dot_v_cb_stmt = dotp(d, p, pv, sub_cb);
    let h2_ty = equiv(d, p, dot_v_cb_stmt, zero);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    // Unfold h1, h2 through dot_sub_right into folded-dot sums ~ 0.
    let dsr1 = d.lemma(p.dot_sub_right, &[pv, pb, pa]);
    let dot_v_ba = dotp(d, p, pv, sub_ba);
    let dot_vb = dotp(d, p, pv, pb);
    let dot_va = dotp(d, p, pv, pa);
    let neg_dot_va = cneg(d, p, dot_va);
    let rhs1 = cadd(d, p, dot_vb, neg_dot_va);
    let dsr1_symm = symm(d, p, dot_v_ba, rhs1, dsr1);
    let eq1_dots = chain(d, p, rhs1, &[(dot_v_ba, dsr1_symm), (zero, h1)]); // Equiv(rhs1, zero)

    let dsr2 = d.lemma(p.dot_sub_right, &[pv, pc, pb]);
    let dot_v_cb = dotp(d, p, pv, sub_cb);
    let dot_vc = dotp(d, p, pv, pc);
    let neg_dot_vb = cneg(d, p, dot_vb);
    let rhs2 = cadd(d, p, dot_vc, neg_dot_vb);
    let dsr2_symm = symm(d, p, dot_v_cb, rhs2, dsr2);
    let eq2_dots = chain(d, p, rhs2, &[(dot_v_cb, dsr2_symm), (zero, h2)]); // Equiv(rhs2, zero)

    // Regroup into raw factored form matching `cross_raw`'s u,v,w,z.
    let (regroup1, u, w) = regroup_dot_diff_proof(d, p, vx, vy, bx, by, ax, ay);
    let (regroup2, z, v_factor) = regroup_dot_diff_proof(d, p, vx, vy, cx, cy, bx, by);

    let vxu = cmul(d, p, vx, u);
    let vyw = cmul(d, p, vy, w);
    let vxz = cmul(d, p, vx, z);
    let vyv = cmul(d, p, vy, v_factor);
    let eq1_target = cadd(d, p, vxu, vyw);
    let eq2_target = cadd(d, p, vxz, vyv);

    let regroup1_symm = symm(d, p, rhs1, eq1_target, regroup1);
    let eq1_f = chain(d, p, eq1_target, &[(rhs1, regroup1_symm), (zero, eq1_dots)]); // Equiv(eq1_target, zero)
    let regroup2_symm = symm(d, p, rhs2, eq2_target, regroup2);
    let eq2_f = chain(d, p, eq2_target, &[(rhs2, regroup2_symm), (zero, eq2_dots)]); // Equiv(eq2_target, zero)

    // D_raw := u*v - w*z, matching `cross A B C`'s own `cross_raw` shape.
    let uv = cmul(d, p, u, v_factor);
    let wz = cmul(d, p, w, z);
    let zw = cmul(d, p, z, w);
    let neg_wz = cneg(d, p, wz);
    let d_raw = cadd(d, p, uv, neg_wz);

    // --- vx * D_raw ~ 0. ---
    // multiply eq1_f by v_factor: (vx*u)*v + (vy*w)*v ~ 0.
    let big_a = cmul(d, p, vxu, v_factor);
    let big_b = cmul(d, p, vyw, v_factor);
    let sum_ab = cadd(d, p, big_a, big_b);
    let rd1 = right_distrib_proof(d, p, vxu, vyw, v_factor); // Equiv(eq1_target*v, sum_ab)
    let eq1_target_v = cmul(d, p, eq1_target, v_factor);
    let zero_v = cmul(d, p, zero, v_factor);
    let refl_v = refl(d, p, v_factor);
    let congr_e1v = d.lemma(
        creal.mul_congr,
        &[eq1_target, zero, v_factor, v_factor, eq1_f, refl_v],
    );
    let zmv = zero_mul_proof(d, p, v_factor);
    let e1v_zero = chain(d, p, eq1_target_v, &[(zero_v, congr_e1v), (zero, zmv)]);
    let rd1_symm = symm(d, p, eq1_target_v, sum_ab, rd1);
    let hab = chain(d, p, sum_ab, &[(eq1_target_v, rd1_symm), (zero, e1v_zero)]);

    // multiply eq2_f by w: (vx*z)*w + (vy*v)*w ~ 0.
    let big_c = cmul(d, p, vxz, w);
    let big_d_ = cmul(d, p, vyv, w);
    let sum_cd = cadd(d, p, big_c, big_d_);
    let rd2 = right_distrib_proof(d, p, vxz, vyv, w);
    let eq2_target_w = cmul(d, p, eq2_target, w);
    let zero_w = cmul(d, p, zero, w);
    let refl_w = refl(d, p, w);
    let congr_e2w = d.lemma(creal.mul_congr, &[eq2_target, zero, w, w, eq2_f, refl_w]);
    let zmw = zero_mul_proof(d, p, w);
    let e2w_zero = chain(d, p, eq2_target_w, &[(zero_w, congr_e2w), (zero, zmw)]);
    let rd2_symm = symm(d, p, eq2_target_w, sum_cd, rd2);
    let hcd = chain(d, p, sum_cd, &[(eq2_target_w, rd2_symm), (zero, e2w_zero)]);

    let h_bd = mul_swap_inner_proof(d, p, vy, w, v_factor); // Equiv(big_b, big_d_)
    let h_ac = elim_step_proof(d, p, big_a, big_b, big_c, big_d_, hab, hcd, h_bd); // Equiv(big_a, big_c)

    let a_prime = cmul(d, p, vx, uv);
    let assoc_a = d.lemma(creal.mul_assoc, &[vx, u, v_factor]); // Equiv(big_a, a_prime)
    let c_pre = cmul(d, p, vx, zw);
    let assoc_c = d.lemma(creal.mul_assoc, &[vx, z, w]); // Equiv(big_c, c_pre)
    let comm_zw = d.lemma(creal.mul_comm, &[z, w]); // Equiv(zw, wz)
    let refl_vx = refl(d, p, vx);
    let congr_c = d.lemma(creal.mul_congr, &[vx, vx, zw, wz, refl_vx, comm_zw]); // Equiv(c_pre, c_pp)
    let c_pp = cmul(d, p, vx, wz);

    let assoc_a_symm = symm(d, p, big_a, a_prime, assoc_a);
    let a_to_cpp = chain(
        d,
        p,
        a_prime,
        &[
            (big_a, assoc_a_symm),
            (big_c, h_ac),
            (c_pre, assoc_c),
            (c_pp, congr_c),
        ],
    ); // Equiv(a_prime, c_pp)

    let msr_vx = mul_sub_right_proof(d, p, vx, uv, wz); // Equiv(vx*D_raw, add a_prime (neg c_pp))
    let cpn_vx = cancel_pos_neg(d, p, a_prime, c_pp, a_to_cpp); // Equiv(add a_prime(neg c_pp), zero)
    let mul_vx_draw = cmul(d, p, vx, d_raw);
    let neg_c_pp = cneg(d, p, c_pp);
    let add_ap_negcpp = cadd(d, p, a_prime, neg_c_pp);
    let result_vx = chain(
        d,
        p,
        mul_vx_draw,
        &[(add_ap_negcpp, msr_vx), (zero, cpn_vx)],
    );

    // --- vy * D_raw ~ 0. ---
    // multiply eq1_f by z: (vx*u)*z + (vy*w)*z ~ 0.
    let big_e = cmul(d, p, vxu, z);
    let big_f = cmul(d, p, vyw, z);
    let sum_ef = cadd(d, p, big_e, big_f);
    let rd3 = right_distrib_proof(d, p, vxu, vyw, z);
    let eq1_target_z = cmul(d, p, eq1_target, z);
    let zero_z = cmul(d, p, zero, z);
    let refl_z = refl(d, p, z);
    let congr_e1z = d.lemma(creal.mul_congr, &[eq1_target, zero, z, z, eq1_f, refl_z]);
    let zmz = zero_mul_proof(d, p, z);
    let e1z_zero = chain(d, p, eq1_target_z, &[(zero_z, congr_e1z), (zero, zmz)]);
    let rd3_symm = symm(d, p, eq1_target_z, sum_ef, rd3);
    let hef = chain(d, p, sum_ef, &[(eq1_target_z, rd3_symm), (zero, e1z_zero)]);

    // multiply eq2_f by u: (vx*z)*u + (vy*v)*u ~ 0.
    let big_g = cmul(d, p, vxz, u);
    let big_h = cmul(d, p, vyv, u);
    let sum_gh = cadd(d, p, big_g, big_h);
    let rd4 = right_distrib_proof(d, p, vxz, vyv, u);
    let eq2_target_u = cmul(d, p, eq2_target, u);
    let zero_u = cmul(d, p, zero, u);
    let refl_u = refl(d, p, u);
    let congr_e2u = d.lemma(creal.mul_congr, &[eq2_target, zero, u, u, eq2_f, refl_u]);
    let zmu = zero_mul_proof(d, p, u);
    let e2u_zero = chain(d, p, eq2_target_u, &[(zero_u, congr_e2u), (zero, zmu)]);
    let rd4_symm = symm(d, p, eq2_target_u, sum_gh, rd4);
    let hgh = chain(d, p, sum_gh, &[(eq2_target_u, rd4_symm), (zero, e2u_zero)]);

    let h_eg = mul_swap_inner_proof(d, p, vx, u, z); // Equiv(big_e, big_g)

    let comm_ef = d.lemma(creal.add_comm, &[big_f, big_e]); // Equiv(add F E, add E F) = Equiv(sum_fe, sum_ef)
    let sum_fe = cadd(d, p, big_f, big_e);
    let h_fe = chain(d, p, sum_fe, &[(sum_ef, comm_ef), (zero, hef)]);

    let comm_gh = d.lemma(creal.add_comm, &[big_h, big_g]); // Equiv(sum_hg, sum_gh)
    let sum_hg = cadd(d, p, big_h, big_g);
    let h_hg = chain(d, p, sum_hg, &[(sum_gh, comm_gh), (zero, hgh)]);

    let h_fh = elim_step_proof(d, p, big_f, big_e, big_h, big_g, h_fe, h_hg, h_eg); // Equiv(big_f, big_h)

    let f_prime = cmul(d, p, vy, wz);
    let assoc_f = d.lemma(creal.mul_assoc, &[vy, w, z]); // Equiv(big_f, f_prime)
    let vu = cmul(d, p, v_factor, u);
    let h_pre = cmul(d, p, vy, vu);
    let assoc_h = d.lemma(creal.mul_assoc, &[vy, v_factor, u]); // Equiv(big_h, h_pre)
    let comm_vu = d.lemma(creal.mul_comm, &[v_factor, u]); // Equiv(vu, uv)
    let refl_vy = refl(d, p, vy);
    let congr_h = d.lemma(creal.mul_congr, &[vy, vy, vu, uv, refl_vy, comm_vu]); // Equiv(h_pre, h_pp)
    let h_pp = cmul(d, p, vy, uv);

    let h_to_hpp = chain(d, p, big_h, &[(h_pre, assoc_h), (h_pp, congr_h)]); // Equiv(big_h, h_pp)
    let h_pp_to_h = symm(d, p, big_h, h_pp, h_to_hpp); // Equiv(h_pp, big_h)
    let h_to_f = symm(d, p, big_f, big_h, h_fh); // Equiv(big_h, big_f)
    let final_vy_pre = chain(
        d,
        p,
        h_pp,
        &[(big_h, h_pp_to_h), (big_f, h_to_f), (f_prime, assoc_f)],
    );
    // final_vy_pre : Equiv(h_pp, f_prime)

    let msr_vy = mul_sub_right_proof(d, p, vy, uv, wz); // Equiv(vy*D_raw, add h_pp (neg f_prime))
    let cpn_vy = cancel_pos_neg(d, p, h_pp, f_prime, final_vy_pre);
    let mul_vy_draw = cmul(d, p, vy, d_raw);
    let neg_f_prime = cneg(d, p, f_prime);
    let add_hpp_negfprime = cadd(d, p, h_pp, neg_f_prime);
    let result_vy = chain(
        d,
        p,
        mul_vy_draw,
        &[(add_hpp_negfprime, msr_vy), (zero, cpn_vy)],
    );

    // Package as the folded-cross-typed conclusion.
    let cross_abc = d.const_app(p.cross, &[pa, pb, pc]);
    let mul_vx_cross = cmul(d, p, vx, cross_abc);
    let concl_x_ty = equiv(d, p, mul_vx_cross, zero);
    let mul_vy_cross = cmul(d, p, vy, cross_abc);
    let concl_y_ty = equiv(d, p, mul_vy_cross, zero);
    let body = and_intro(d, p, concl_x_ty, concl_y_ty, result_vx, result_vy);
    let concl = d.and(concl_x_ty, concl_y_ty);

    let ty_body = {
        let inner = d.arrow(h2_ty, concl);
        d.arrow(h1_ty, inner)
    };
    let ty = {
        let w4 = d.pi_fv(c_fv, point, ty_body);
        let w3 = d.pi_fv(b_fv, point, w4);
        let w2 = d.pi_fv(a_fv, point, w3);
        d.pi_fv(v_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h2_fv, h2_ty, body);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, inner);
        let w4 = d.lam_fv(c_fv, point, with_h1);
        let w3 = d.lam_fv(b_fv, point, w4);
        let w2 = d.lam_fv(a_fv, point, w3);
        d.lam_fv(v_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cross_annihilates_difference,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The headline: three non-collinear points determine a unique
/// circumcentre.** See [`CPointPrelude::circumcentre_unique`].
fn declare_circumcentre_unique(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let pk = d.kernel().fvar(k_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let op_fv = d.fresh_fvar();
    let pop = d.kernel().fvar(op_fv);

    let nc_ty = d.const_app(p.non_collinear, &[pa, pb, pc, pk]);
    let nc_fv = d.fresh_fvar();
    let hnc = d.kernel().fvar(nc_fv);

    let dsq_oa = d.const_app(p.dist_sq, &[po, pa]);
    let dsq_ob = d.const_app(p.dist_sq, &[po, pb]);
    let dsq_oc = d.const_app(p.dist_sq, &[po, pc]);
    let dsq_opa = d.const_app(p.dist_sq, &[pop, pa]);
    let dsq_opb = d.const_app(p.dist_sq, &[pop, pb]);
    let dsq_opc = d.const_app(p.dist_sq, &[pop, pc]);

    let h1_ty = equiv(d, p, dsq_oa, dsq_ob);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = equiv(d, p, dsq_ob, dsq_oc);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h1p_ty = equiv(d, p, dsq_opa, dsq_opb);
    let h1p_fv = d.fresh_fvar();
    let h1p = d.kernel().fvar(h1p_fv);
    let h2p_ty = equiv(d, p, dsq_opb, dsq_opc);
    let h2p_fv = d.fresh_fvar();
    let h2p = d.kernel().fvar(h2p_fv);

    // Step 1: dot(O-O', B-A) ~ 0, dot(O-O', C-B) ~ 0.
    let hdiff = d.lemma(
        p.circumcentre_difference_dots,
        &[po, pop, pa, pb, pc, h1, h2, h1p, h2p],
    );
    let sub_ba = psub(d, p, pb, pa);
    let sub_cb = psub(d, p, pc, pb);
    let sub_oop = psub(d, p, po, pop);
    let zero = czero(d, p);
    let dot_oop_ba = dotp(d, p, sub_oop, sub_ba);
    let concl_ab_ty = equiv(d, p, dot_oop_ba, zero);
    let dot_oop_cb = dotp(d, p, sub_oop, sub_cb);
    let concl_bc_ty = equiv(d, p, dot_oop_cb, zero);
    let hd1 = d.and_left(concl_ab_ty, concl_bc_ty, hdiff);
    let hd2 = d.and_right(concl_ab_ty, concl_bc_ty, hdiff);

    // Step 2: annihilated by the determinant.
    let hca = d.lemma(
        p.cross_annihilates_difference,
        &[sub_oop, pa, pb, pc, hd1, hd2],
    );
    let vx = d.const_app(p.x, &[sub_oop]);
    let vy = d.const_app(p.y, &[sub_oop]);
    let cross_abc = d.const_app(p.cross, &[pa, pb, pc]);
    let mul_vx_cross = cmul(d, p, vx, cross_abc);
    let concl_x_ty = equiv(d, p, mul_vx_cross, zero);
    let mul_vy_cross = cmul(d, p, vy, cross_abc);
    let concl_y_ty = equiv(d, p, mul_vy_cross, zero);
    let hvx_d = d.and_left(concl_x_ty, concl_y_ty, hca);
    let hvy_d = d.and_right(concl_x_ty, concl_y_ty, hca);

    // Step 3: cancel the determinant via the witnessed inverse.
    let vx_zero = cancel_via_pos_bound_proof(d, p, vx, cross_abc, pk, hnc, hvx_d);
    let vy_zero = cancel_via_pos_bound_proof(d, p, vy, cross_abc, pk, hnc, hvy_d);

    // Step 4: read back as CPoint.Equiv O O'.
    let ox = d.const_app(p.x, &[po]);
    let oy = d.const_app(p.y, &[po]);
    let opx = d.const_app(p.x, &[pop]);
    let opy = d.const_app(p.y, &[pop]);
    let ox_eq_opx = equiv_of_sub_eq_zero(d, p, ox, opx, vx_zero);
    let oy_eq_opy = equiv_of_sub_eq_zero(d, p, oy, opy, vy_zero);

    let claim_x = equiv(d, p, ox, opx);
    let claim_y = equiv(d, p, oy, opy);
    let body = and_intro(d, p, claim_x, claim_y, ox_eq_opx, oy_eq_opy);
    let concl_final = d.const_app(p.point_equiv, &[po, pop]);

    let ty_body = {
        let inner = d.arrow(h2p_ty, concl_final);
        let with_h1p = d.arrow(h1p_ty, inner);
        let with_h2 = d.arrow(h2_ty, with_h1p);
        let with_h1 = d.arrow(h1_ty, with_h2);
        d.arrow(nc_ty, with_h1)
    };
    let ty = {
        let w6 = d.pi_fv(op_fv, point, ty_body);
        let w5 = d.pi_fv(o_fv, point, w6);
        let w4 = d.pi_fv(c_fv, point, w5);
        let w3 = d.pi_fv(b_fv, point, w4);
        let w2 = d.pi_fv(a_fv, point, w3);
        d.pi_fv(k_fv, nat, w2)
    };
    let value = {
        let inner = d.lam_fv(h2p_fv, h2p_ty, body);
        let with_h1p = d.lam_fv(h1p_fv, h1p_ty, inner);
        let with_h2 = d.lam_fv(h2_fv, h2_ty, with_h1p);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
        let with_nc = d.lam_fv(nc_fv, nc_ty, with_h1);
        let w6 = d.lam_fv(op_fv, point, with_nc);
        let w5 = d.lam_fv(o_fv, point, w6);
        let w4 = d.lam_fv(c_fv, point, w5);
        let w3 = d.lam_fv(b_fv, point, w4);
        let w2 = d.lam_fv(a_fv, point, w3);
        d.lam_fv(k_fv, nat, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.circumcentre_unique,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the power of a point, and the radical axis -----------------------------

/// `CPoint.power P O r2`.
fn powerp(d: &mut IntDev<'_>, p: CPointPrelude, pt: ExprId, o: ExprId, r2: ExprId) -> ExprId {
    d.const_app(p.power, &[pt, o, r2])
}

/// `CPoint.power P O r2 := CPoint.distSq P O + CReal.neg r2`. See
/// [`CPointPrelude::power`].
fn declare_power(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let dsq_po = d.const_app(p.dist_sq, &[pp, po]);
    let neg_r = cneg(d, p, r);
    let value_body = cadd(d, p, dsq_po, neg_r);

    let value = {
        let inner = d.lam_fv(r_fv, carrier, value_body);
        let mid = d.lam_fv(o_fv, point, inner);
        d.lam_fv(pp_fv, point, mid)
    };
    let ty = {
        let inner = d.arrow(carrier, carrier);
        let mid = d.arrow(point, inner);
        d.arrow(point, mid)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.power,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 19),
    })
}

/// **The power vanishes exactly on the circle.** See
/// [`CPointPrelude::power_zero_iff_on_circle`].
fn declare_power_zero_iff_on_circle(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let logic = creal.rat.int.logic;
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let power_term = powerp(d, p, pp, po, r);
    let zero = czero(d, p);
    let power_zero_ty = equiv(d, p, power_term, zero);
    let on_circle_ty = d.const_app(p.on_circle, &[pp, po, r]);
    let dsq_po = d.const_app(p.dist_sq, &[pp, po]);

    let mp_body = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = equiv_of_sub_eq_zero(d, p, dsq_po, r, h);
        d.lam_fv(h_fv, power_zero_ty, body)
    };
    let mpr_body = {
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let body = sub_eq_zero_of_equiv(d, p, dsq_po, r, hc);
        d.lam_fv(hc_fv, on_circle_ty, body)
    };

    let iff_stmt = d.const_app(logic.iff, &[power_zero_ty, on_circle_ty]);
    let iff_proof = d.const_app(
        logic.iff_intro,
        &[power_zero_ty, on_circle_ty, mp_body, mpr_body],
    );

    let ty = {
        let inner = d.pi_fv(r_fv, carrier, iff_stmt);
        let mid = d.pi_fv(o_fv, point, inner);
        d.pi_fv(pp_fv, point, mid)
    };
    let value = {
        let inner = d.lam_fv(r_fv, carrier, iff_proof);
        let mid = d.lam_fv(o_fv, point, inner);
        d.lam_fv(pp_fv, point, mid)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_zero_iff_on_circle,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The power of the centre.** See [`CPointPrelude::power_of_centre`].
fn declare_power_of_centre(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let creal = p.creal;

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let dsz = d.lemma(p.dist_sq_self_zero, &[po]); // Equiv (distSq O O) zero
    let dsq_oo = d.const_app(p.dist_sq, &[po, po]);
    let neg_r = cneg(d, p, r);
    let zero = czero(d, p);
    let refl_negr = refl(d, p, neg_r);
    let congr = d.lemma(
        creal.add_congr,
        &[dsq_oo, zero, neg_r, neg_r, dsz, refl_negr],
    );
    let sum = cadd(d, p, dsq_oo, neg_r); // == power O O r2, unfolded
    let zero_negr = cadd(d, p, zero, neg_r);
    let za = zero_add_proof(d, p, neg_r); // Equiv(zero_negr, neg_r)
    let proof = chain(d, p, sum, &[(zero_negr, congr), (neg_r, za)]);

    let power_term = powerp(d, p, po, po, r);
    let ty_body = equiv(d, p, power_term, neg_r);
    let ty = {
        let inner = d.pi_fv(r_fv, carrier, ty_body);
        d.pi_fv(o_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(r_fv, carrier, proof);
        d.lam_fv(o_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_of_centre,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (mul CPoint.Scalar.inv2 (add x x)) x` — halving a doubled scalar,
/// the "Route B" half of [`zero_of_double_zero`] extracted so it is usable
/// at a target other than zero (that function is not touched — see the
/// module's "do not perturb a working proof" convention).
fn half_of_double_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let two = d.kernel().const_(p.two, vec![]);
    let one = d.kernel().const_(creal.one, vec![]);
    let x_x = cadd(d, p, x, x);
    let inv2_xx = cmul(d, p, inv2, x_x);
    let refl_inv2 = refl(d, p, inv2);

    let two_x = cmul(d, p, two, x);
    let tmed = two_mul_eq_double_proof(d, p, x); // Equiv(two_x, x_x)
    let tmed_symm = symm(d, p, two_x, x_x, tmed); // Equiv(x_x, two_x)
    let congr1 = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, x_x, two_x, refl_inv2, tmed_symm],
    );
    let inv2_two_x = cmul(d, p, inv2, two_x);

    let inv2_two = cmul(d, p, inv2, two);
    let inv2_two_via_x = cmul(d, p, inv2_two, x);
    let assoc = d.lemma(creal.mul_assoc, &[inv2, two, x]); // Equiv(inv2_two_via_x, inv2_two_x)
    let assoc_symm = symm(d, p, inv2_two_via_x, inv2_two_x, assoc);

    let two_inv2 = cmul(d, p, two, inv2);
    let comm = d.lemma(creal.mul_comm, &[inv2, two]); // Equiv(inv2_two, two_inv2)
    let zero_nat = d.num(0);
    let h_two = d.kernel().const_(p.two_pos_bound, vec![]);
    let cancel = d.lemma(creal.mul_inv_cancel, &[two, zero_nat, h_two]); // Equiv(two_inv2, one)
    let inv2_two_is_one = chain(d, p, inv2_two, &[(two_inv2, comm), (one, cancel)]);

    let refl_x = refl(d, p, x);
    let congr2 = d.lemma(
        creal.mul_congr,
        &[inv2_two, one, x, x, inv2_two_is_one, refl_x],
    );
    let one_x = cmul(d, p, one, x);
    let omp = one_mul_proof(d, p, x); // Equiv(one_x, x)

    chain(
        d,
        p,
        inv2_xx,
        &[
            (inv2_two_x, congr1),
            (inv2_two_via_x, assoc_symm),
            (one_x, congr2),
            (x, omp),
        ],
    )
}

/// `Equiv (add (mul CPoint.Scalar.inv2 v) (mul CPoint.Scalar.inv2 v)) v` —
/// doubling a halved scalar, the mirror of [`half_of_double_proof`].
fn double_half_proof(d: &mut IntDev<'_>, p: CPointPrelude, v: ExprId) -> ExprId {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let two = d.kernel().const_(p.two, vec![]);
    let one = d.kernel().const_(creal.one, vec![]);

    let inv2v = cmul(d, p, inv2, v);
    let sum = cadd(d, p, inv2v, inv2v);
    let two_inv2v = cmul(d, p, two, inv2v);
    let tmed = two_mul_eq_double_proof(d, p, inv2v); // Equiv(two_inv2v, sum)
    let sum_eq_two_inv2v = symm(d, p, two_inv2v, sum, tmed); // Equiv(sum, two_inv2v)

    let two_inv2 = cmul(d, p, two, inv2);
    let mul_two_inv2_v = cmul(d, p, two_inv2, v);
    let assoc = d.lemma(creal.mul_assoc, &[two, inv2, v]); // Equiv(mul_two_inv2_v, two_inv2v)
    let assoc_symm = symm(d, p, mul_two_inv2_v, two_inv2v, assoc);

    let zero_nat = d.num(0);
    let h_two = d.kernel().const_(p.two_pos_bound, vec![]);
    let cancel = d.lemma(creal.mul_inv_cancel, &[two, zero_nat, h_two]); // Equiv(two_inv2, one)
    let refl_v = refl(d, p, v);
    let congr = d.lemma(creal.mul_congr, &[two_inv2, one, v, v, cancel, refl_v]);
    let one_v = cmul(d, p, one, v);
    let omp = one_mul_proof(d, p, v); // Equiv(one_v, v)

    chain(
        d,
        p,
        sum,
        &[
            (two_inv2v, sum_eq_two_inv2v),
            (mul_two_inv2_v, assoc_symm),
            (one_v, congr),
            (v, omp),
        ],
    )
}

/// `Equiv (add (neg a) b) (neg (add a (neg b)))`.
fn neg_add_neg_swap_proof(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    let creal = p.creal;
    let neg_a = cneg(d, p, a);
    let neg_b = cneg(d, p, b);
    let v = cadd(d, p, a, neg_b); // a - b
    let neg_v = cneg(d, p, v);

    let na = neg_add_proof(d, p, a, neg_b); // Equiv (neg v) (add neg_a (neg neg_b))
    let neg_neg_b = cneg(d, p, neg_b);
    let neg_a_neg_neg_b = cadd(d, p, neg_a, neg_neg_b);

    let nnb = neg_neg_proof(d, p, b); // Equiv (neg neg_b) b
    let refl_neg_a = refl(d, p, neg_a);
    let congr = d.lemma(
        creal.add_congr,
        &[neg_a, neg_a, neg_neg_b, b, refl_neg_a, nnb],
    );
    let neg_a_b = cadd(d, p, neg_a, b);

    let route = chain(d, p, neg_v, &[(neg_a_neg_neg_b, na), (neg_a_b, congr)]);
    symm(d, p, neg_v, neg_a_b, route)
}

/// **The distSq-difference doubles the midpoint-dot.** Duplicates
/// [`declare_perp_bisector_iff_dot`]'s own `ident` derivation (this file's
/// established convention: a working proof is not refactored to be shared —
/// see [`declare_thales`]/[`declare_thales_converse`]), generalized from a
/// segment's two endpoints to two independent centres. Returns `(X, distSq P
/// O1, distSq P O2, proof)` where `X := dot (sub P (midpoint O1 O2)) (sub O2
/// O1)` and `proof : Equiv (add (distSq P O1) (neg (distSq P O2))) (add X
/// X)`.
fn distsq_diff_double_dot_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    pp: ExprId,
    o1: ExprId,
    o2: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let creal = p.creal;
    let px = d.const_app(p.x, &[pp]);
    let py = d.const_app(p.y, &[pp]);
    let ax = d.const_app(p.x, &[o1]);
    let ay = d.const_app(p.y, &[o1]);
    let bx = d.const_app(p.x, &[o2]);
    let by = d.const_app(p.y, &[o2]);

    let mx = midpoint(d, p, ax, bx);
    let my = midpoint(d, p, ay, by);
    let pm = d.const_app(p.point_midpoint, &[o1, o2]);

    let big_u = psub(d, p, pp, pm);
    let big_v = psub(d, p, pm, o1);
    let big_w = psub(d, p, o2, o1);

    let neg_ax = cneg(d, p, ax);
    let neg_bx = cneg(d, p, bx);
    let neg_mx = cneg(d, p, mx);
    let neg_ay = cneg(d, p, ay);
    let neg_by = cneg(d, p, by);
    let neg_my = cneg(d, p, my);

    let px_mx = cadd(d, p, px, neg_mx);
    let mx_ax = cadd(d, p, mx, neg_ax);
    let px_ax = cadd(d, p, px, neg_ax);
    let u_plus_v_x = cadd(d, p, px_mx, mx_ax);
    let fact_a_x_ty = equiv(d, p, px_ax, u_plus_v_x);
    let fact_a_x = telescope_scalar_proof(d, p, px, mx, ax);

    let py_my = cadd(d, p, py, neg_my);
    let my_ay = cadd(d, p, my, neg_ay);
    let py_ay = cadd(d, p, py, neg_ay);
    let u_plus_v_y = cadd(d, p, py_my, my_ay);
    let fact_a_y_ty = equiv(d, p, py_ay, u_plus_v_y);
    let fact_a_y = telescope_scalar_proof(d, p, py, my, ay);

    let fact_a = and_intro(d, p, fact_a_x_ty, fact_a_y_ty, fact_a_x, fact_a_y);

    let px_bx = cadd(d, p, px, neg_bx);
    let mx_bx = cadd(d, p, mx, neg_bx);
    let step_x = telescope_scalar_proof(d, p, px, mx, bx);
    let px_mx_mx_bx = cadd(d, p, px_mx, mx_bx);
    let mb_x = midpoint_equidistant_scalar_proof(d, p, ax, bx, mx);
    let neg_mx_ax = cneg(d, p, mx_ax);
    let refl_pxmx = refl(d, p, px_mx);
    let congr_bx = d.lemma(
        creal.add_congr,
        &[px_mx, px_mx, mx_bx, neg_mx_ax, refl_pxmx, mb_x],
    );
    let u_minus_v_x = cadd(d, p, px_mx, neg_mx_ax);
    let fact_b_x = chain(
        d,
        p,
        px_bx,
        &[(px_mx_mx_bx, step_x), (u_minus_v_x, congr_bx)],
    );
    let fact_b_x_ty = equiv(d, p, px_bx, u_minus_v_x);

    let py_by = cadd(d, p, py, neg_by);
    let my_by = cadd(d, p, my, neg_by);
    let step_y = telescope_scalar_proof(d, p, py, my, by);
    let py_my_my_by = cadd(d, p, py_my, my_by);
    let mb_y = midpoint_equidistant_scalar_proof(d, p, ay, by, my);
    let neg_my_ay = cneg(d, p, my_ay);
    let refl_pymy = refl(d, p, py_my);
    let congr_by = d.lemma(
        creal.add_congr,
        &[py_my, py_my, my_by, neg_my_ay, refl_pymy, mb_y],
    );
    let u_minus_v_y = cadd(d, p, py_my, neg_my_ay);
    let fact_b_y = chain(
        d,
        p,
        py_by,
        &[(py_my_my_by, step_y), (u_minus_v_y, congr_by)],
    );
    let fact_b_y_ty = equiv(d, p, py_by, u_minus_v_y);

    let fact_b = and_intro(d, p, fact_b_x_ty, fact_b_y_ty, fact_b_x, fact_b_y);

    let mx_ax_mx_ax = cadd(d, p, mx_ax, mx_ax);
    let bx_ax = cadd(d, p, bx, neg_ax);
    let wfact_x = half_diff_double_proof(d, p, ax, bx, mx);
    let wfact_x_symm = symm(d, p, mx_ax_mx_ax, bx_ax, wfact_x);
    let my_ay_my_ay = cadd(d, p, my_ay, my_ay);
    let by_ay = cadd(d, p, by, neg_ay);
    let wfact_y = half_diff_double_proof(d, p, ay, by, my);
    let wfact_y_symm = symm(d, p, my_ay_my_ay, by_ay, wfact_y);
    let w_x_ty = equiv(d, p, bx_ax, mx_ax_mx_ax);
    let w_y_ty = equiv(d, p, by_ay, my_ay_my_ay);
    let w_fact = and_intro(d, p, w_x_ty, w_y_ty, wfact_x_symm, wfact_y_symm);

    let sub_pa = psub(d, p, pp, o1);
    let sub_pb = psub(d, p, pp, o2);
    let u_plus_v = padd(d, p, big_u, big_v);
    let u_minus_v = psub(d, p, big_u, big_v);

    let dcongr_a = d.lemma(
        p.dot_congr,
        &[sub_pa, u_plus_v, sub_pa, u_plus_v, fact_a, fact_a],
    );
    let dsq_pa = dotp(d, p, sub_pa, sub_pa);
    let dot_upv_upv = dotp(d, p, u_plus_v, u_plus_v);
    let dsa = d.lemma(p.dot_self_add, &[big_u, big_v]);
    let x_ = dotp(d, p, big_u, big_u);
    let y_ = dotp(d, p, big_u, big_v);
    let z_ = dotp(d, p, big_v, big_v);
    let y_z = cadd(d, p, y_, z_);
    let y_y_z = cadd(d, p, y_, y_z);
    let term_add = cadd(d, p, x_, y_y_z);
    let dsq_pa_expand = chain(d, p, dsq_pa, &[(dot_upv_upv, dcongr_a), (term_add, dsa)]);

    let dcongr_b = d.lemma(
        p.dot_congr,
        &[sub_pb, u_minus_v, sub_pb, u_minus_v, fact_b, fact_b],
    );
    let dsq_pb = dotp(d, p, sub_pb, sub_pb);
    let dot_umv_umv = dotp(d, p, u_minus_v, u_minus_v);
    let dss = d.lemma(p.dot_self_sub, &[big_u, big_v]);
    let neg_y = cneg(d, p, y_);
    let neg_y_z = cadd(d, p, neg_y, z_);
    let neg_y_neg_y_z = cadd(d, p, neg_y, neg_y_z);
    let term_sub = cadd(d, p, x_, neg_y_neg_y_z);
    let dsq_pb_expand = chain(d, p, dsq_pb, &[(dot_umv_umv, dcongr_b), (term_sub, dss)]);

    let combine = perp_bisector_combine_proof(d, p, x_, y_, z_);

    let neg_dsq_pb = cneg(d, p, dsq_pb);
    let neg_term_sub = cneg(d, p, term_sub);
    let neg_congr = d.lemma(creal.neg_congr, &[dsq_pb, term_sub, dsq_pb_expand]);
    let diff_ab = cadd(d, p, dsq_pa, neg_dsq_pb);
    let refl_dsqpa = refl(d, p, dsq_pa);
    let step_diff1 = d.lemma(
        creal.add_congr,
        &[
            dsq_pa,
            dsq_pa,
            neg_dsq_pb,
            neg_term_sub,
            refl_dsqpa,
            neg_congr,
        ],
    );
    let dsq_pa_neg_term_sub = cadd(d, p, dsq_pa, neg_term_sub);
    let refl_negts = refl(d, p, neg_term_sub);
    let step_diff2 = d.lemma(
        creal.add_congr,
        &[
            dsq_pa,
            term_add,
            neg_term_sub,
            neg_term_sub,
            dsq_pa_expand,
            refl_negts,
        ],
    );
    let term_add_neg_term_sub = cadd(d, p, term_add, neg_term_sub);
    let yy = cadd(d, p, y_, y_);
    let target = cadd(d, p, yy, yy);

    let diff_ab_expand = chain(
        d,
        p,
        diff_ab,
        &[
            (dsq_pa_neg_term_sub, step_diff1),
            (term_add_neg_term_sub, step_diff2),
            (target, combine),
        ],
    );

    let big_x = dotp(d, p, big_u, big_w);
    let v_plus_v = padd(d, p, big_v, big_v);
    let refl_u = point_equiv_refl(d, p, big_u);
    let dcongr_x = d.lemma(
        p.dot_congr,
        &[big_u, big_u, big_w, v_plus_v, refl_u, w_fact],
    );
    let dot_u_vpv = dotp(d, p, big_u, v_plus_v);
    let dar = d.lemma(p.dot_add_right, &[big_u, big_v, big_v]);
    let x_eq_yy = chain(d, p, big_x, &[(dot_u_vpv, dcongr_x), (yy, dar)]);

    let x_eq_yy_symm = symm(d, p, big_x, yy, x_eq_yy);
    let congr_xx = d.lemma(
        creal.add_congr,
        &[yy, big_x, yy, big_x, x_eq_yy_symm, x_eq_yy_symm],
    );
    let x_plus_x = cadd(d, p, big_x, big_x);
    let ident = chain(
        d,
        p,
        diff_ab,
        &[(target, diff_ab_expand), (x_plus_x, congr_xx)],
    );

    (big_x, dsq_pa, dsq_pb, ident)
}

/// **The power difference doubles the midpoint-dot, offset by the radii.**
/// `power P O1 r1 − power P O2 r2 ~ (X+X) + (neg r1 + r2)`, `X` as in
/// [`distsq_diff_double_dot_proof`] — the shared algebraic core behind
/// [`declare_radical_axis_iff_dot`] and [`declare_power_difference_linear`].
fn power_diff_ident_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    pp: ExprId,
    o1: ExprId,
    o2: ExprId,
    r1: ExprId,
    r2: ExprId,
) -> (ExprId, ExprId) {
    let creal = p.creal;
    let (big_x, dsq1, dsq2, ident) = distsq_diff_double_dot_proof(d, p, pp, o1, o2);

    let neg_r1 = cneg(d, p, r1);
    let neg_r2 = cneg(d, p, r2);
    let power1 = cadd(d, p, dsq1, neg_r1);
    let power2 = cadd(d, p, dsq2, neg_r2);
    let neg_power2 = cneg(d, p, power2);

    // neg power2 ~ neg dsq2 + r2.
    let na = neg_add_proof(d, p, dsq2, neg_r2);
    let neg_dsq2 = cneg(d, p, dsq2);
    let neg_neg_r2 = cneg(d, p, neg_r2);
    let neg_dsq2_neg_neg_r2 = cadd(d, p, neg_dsq2, neg_neg_r2);
    let nnr2 = neg_neg_proof(d, p, r2);
    let refl_neg_dsq2 = refl(d, p, neg_dsq2);
    let congr_a = d.lemma(
        creal.add_congr,
        &[neg_dsq2, neg_dsq2, neg_neg_r2, r2, refl_neg_dsq2, nnr2],
    );
    let neg_dsq2_r2 = cadd(d, p, neg_dsq2, r2);
    let neg_power2_eq = chain(
        d,
        p,
        neg_power2,
        &[(neg_dsq2_neg_neg_r2, na), (neg_dsq2_r2, congr_a)],
    );

    // power1 + neg power2 ~ power1 + (neg dsq2 + r2).
    let refl_power1 = refl(d, p, power1);
    let congr_b = d.lemma(
        creal.add_congr,
        &[
            power1,
            power1,
            neg_power2,
            neg_dsq2_r2,
            refl_power1,
            neg_power2_eq,
        ],
    );
    let power1_negdsq2r2 = cadd(d, p, power1, neg_dsq2_r2);

    // reassociate: (dsq1+neg_r1)+(neg_dsq2+r2) ~ (dsq1+neg_dsq2)+(neg_r1+r2).
    let swap = add_middle_swap_proof(d, p, dsq1, neg_r1, neg_dsq2, r2);
    let dsq1_negdsq2 = cadd(d, p, dsq1, neg_dsq2);
    let negr1_r2 = cadd(d, p, neg_r1, r2);
    let regrouped = cadd(d, p, dsq1_negdsq2, negr1_r2);

    // substitute ident.
    let big_x_x = cadd(d, p, big_x, big_x);
    let refl_negr1r2 = refl(d, p, negr1_r2);
    let congr_d = d.lemma(
        creal.add_congr,
        &[
            dsq1_negdsq2,
            big_x_x,
            negr1_r2,
            negr1_r2,
            ident,
            refl_negr1r2,
        ],
    );
    let bigxx_negr1r2 = cadd(d, p, big_x_x, negr1_r2);

    let power1_neg_power2 = cadd(d, p, power1, neg_power2);
    let main_ident = chain(
        d,
        p,
        power1_neg_power2,
        &[
            (power1_negdsq2r2, congr_b),
            (regrouped, swap),
            (bigxx_negr1r2, congr_d),
        ],
    );
    (big_x, main_ident)
}

/// **The radical axis.** See [`CPointPrelude::radical_axis_iff_dot`].
fn declare_radical_axis_iff_dot(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let logic = creal.rat.int.logic;
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

    let o1_fv = d.fresh_fvar();
    let po1 = d.kernel().fvar(o1_fv);
    let o2_fv = d.fresh_fvar();
    let po2 = d.kernel().fvar(o2_fv);
    let r1_fv = d.fresh_fvar();
    let pr1 = d.kernel().fvar(r1_fv);
    let r2_fv = d.fresh_fvar();
    let pr2 = d.kernel().fvar(r2_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let (big_x, main_ident) = power_diff_ident_proof(d, p, pp, po1, po2, pr1, pr2);

    let power1 = powerp(d, p, pp, po1, pr1);
    let power2 = powerp(d, p, pp, po2, pr2);
    let power_iff_ty = equiv(d, p, power1, power2);

    let pm = d.const_app(p.point_midpoint, &[po1, po2]);
    let sub_p_m = psub(d, p, pp, pm);
    let sub_o2_o1 = psub(d, p, po2, po1);
    let dot_stmt_lhs = dotp(d, p, sub_p_m, sub_o2_o1);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let neg_r1 = cneg(d, p, pr1);
    let neg_r2 = cneg(d, p, pr2);
    let v = cadd(d, p, pr1, neg_r2);
    let c = cmul(d, p, inv2, v);
    let dot_stmt = equiv(d, p, dot_stmt_lhs, c);

    let negr1_r2 = cadd(d, p, neg_r1, pr2);
    let big_x_x = cadd(d, p, big_x, big_x);
    let zero = czero(d, p);
    let neg_power2_top = cneg(d, p, power2);
    let power1_neg_power2 = cadd(d, p, power1, neg_power2_top);
    let bigxx_negr1r2 = cadd(d, p, big_x_x, negr1_r2);

    // mp : power1 ~ power2 -> Equiv big_x c.
    let mp_body = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let cpn = cancel_pos_neg(d, p, power1, power2, h); // Equiv power1_neg_power2 zero
        let main_symm = symm(d, p, power1_neg_power2, bigxx_negr1r2, main_ident);
        let target_zero = chain(
            d,
            p,
            bigxx_negr1r2,
            &[(power1_neg_power2, main_symm), (zero, cpn)],
        );

        let swap_proof = neg_add_neg_swap_proof(d, p, pr1, pr2); // Equiv negr1_r2 (neg v)
        let neg_v = cneg(d, p, v);
        let refl_bigxx = refl(d, p, big_x_x);
        let congr_v = d.lemma(
            creal.add_congr,
            &[big_x_x, big_x_x, negr1_r2, neg_v, refl_bigxx, swap_proof],
        );
        let bigxx_negv = cadd(d, p, big_x_x, neg_v);
        let congr_v_symm = symm(d, p, bigxx_negr1r2, bigxx_negv, congr_v);
        let final_zero = chain(
            d,
            p,
            bigxx_negv,
            &[(bigxx_negr1r2, congr_v_symm), (zero, target_zero)],
        );
        let bigxx_eq_v = equiv_of_sub_eq_zero(d, p, big_x_x, v, final_zero);

        let hod = half_of_double_proof(d, p, big_x); // Equiv (mul inv2 big_x_x) big_x
        let inv2_bigxx = cmul(d, p, inv2, big_x_x);
        let hod_symm = symm(d, p, inv2_bigxx, big_x, hod);
        let refl_inv2 = refl(d, p, inv2);
        let congr_c = d.lemma(
            creal.mul_congr,
            &[inv2, inv2, big_x_x, v, refl_inv2, bigxx_eq_v],
        );
        let body = chain(d, p, big_x, &[(inv2_bigxx, hod_symm), (c, congr_c)]);
        d.lam_fv(h_fv, power_iff_ty, body)
    };

    // mpr : Equiv big_x c -> power1 ~ power2.
    let mpr_body = {
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let congr_hc = d.lemma(creal.add_congr, &[big_x, c, big_x, c, hc, hc]);
        let c_c = cadd(d, p, c, c);
        let dhp = double_half_proof(d, p, v); // Equiv (add (mul inv2 v) (mul inv2 v)) v
        let bigxx_eq_v = chain(d, p, big_x_x, &[(c_c, congr_hc), (v, dhp)]);

        let v_negr1r2 = cadd(d, p, v, negr1_r2);
        let swap2 = add_middle_swap_proof(d, p, pr1, neg_r2, neg_r1, pr2);
        let r1_negr1 = cadd(d, p, pr1, neg_r1);
        let negr2_r2 = cadd(d, p, neg_r2, pr2);
        let an_r1 = d.lemma(creal.add_neg, &[pr1]);
        let nac_r2 = neg_add_cancel_proof(d, p, pr2);
        let congr_zeros = d.lemma(
            creal.add_congr,
            &[r1_negr1, zero, negr2_r2, zero, an_r1, nac_r2],
        );
        let zero_zero = cadd(d, p, zero, zero);
        let az = d.lemma(creal.add_zero, &[zero]);
        let r1r1_negr2r2 = cadd(d, p, r1_negr1, negr2_r2);
        let rhs_zero = chain(d, p, r1r1_negr2r2, &[(zero_zero, congr_zeros), (zero, az)]);
        let vw_zero = chain(d, p, v_negr1r2, &[(r1r1_negr2r2, swap2), (zero, rhs_zero)]);

        let refl_negr1r2 = refl(d, p, negr1_r2);
        let congr_vv = d.lemma(
            creal.add_congr,
            &[big_x_x, v, negr1_r2, negr1_r2, bigxx_eq_v, refl_negr1r2],
        );
        let rhs_final_zero = chain(
            d,
            p,
            bigxx_negr1r2,
            &[(v_negr1r2, congr_vv), (zero, vw_zero)],
        );

        let power_diff_zero = chain(
            d,
            p,
            power1_neg_power2,
            &[(bigxx_negr1r2, main_ident), (zero, rhs_final_zero)],
        );
        let body = equiv_of_sub_eq_zero(d, p, power1, power2, power_diff_zero);
        d.lam_fv(hc_fv, dot_stmt, body)
    };

    let iff_stmt = d.const_app(logic.iff, &[power_iff_ty, dot_stmt]);
    let iff_proof = d.const_app(
        logic.iff_intro,
        &[power_iff_ty, dot_stmt, mp_body, mpr_body],
    );

    let ty = {
        let w1 = d.pi_fv(pp_fv, point, iff_stmt);
        let w2 = d.pi_fv(r2_fv, carrier, w1);
        let w3 = d.pi_fv(r1_fv, carrier, w2);
        let w4 = d.pi_fv(o2_fv, point, w3);
        d.pi_fv(o1_fv, point, w4)
    };
    let value = {
        let w1 = d.lam_fv(pp_fv, point, iff_proof);
        let w2 = d.lam_fv(r2_fv, carrier, w1);
        let w3 = d.lam_fv(r1_fv, carrier, w2);
        let w4 = d.lam_fv(o2_fv, point, w3);
        d.lam_fv(o1_fv, point, w4)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.radical_axis_iff_dot,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The power difference is affine in `P`.** See
/// [`CPointPrelude::power_difference_linear`].
fn declare_power_difference_linear(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

    let o1_fv = d.fresh_fvar();
    let po1 = d.kernel().fvar(o1_fv);
    let o2_fv = d.fresh_fvar();
    let po2 = d.kernel().fvar(o2_fv);
    let r1_fv = d.fresh_fvar();
    let pr1 = d.kernel().fvar(r1_fv);
    let r2_fv = d.fresh_fvar();
    let pr2 = d.kernel().fvar(r2_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let (big_x, main_ident) = power_diff_ident_proof(d, p, pp, po1, po2, pr1, pr2);

    let pm = d.const_app(p.point_midpoint, &[po1, po2]);
    let big_w = psub(d, p, po2, po1);
    let dot_pw = dotp(d, p, pp, big_w);
    let dot_mw = dotp(d, p, pm, big_w);

    // big_x ~ dot_pw + neg dot_mw.
    let big_x_expand = d.lemma(p.dot_sub_left, &[pp, pm, big_w]);
    let neg_dot_mw = cneg(d, p, dot_mw);
    let dotpw_negdotmw = cadd(d, p, dot_pw, neg_dot_mw);

    // big_x_x ~ (dotpw_negdotmw)+(dotpw_negdotmw).
    let congr_xx = d.lemma(
        creal.add_congr,
        &[
            big_x,
            dotpw_negdotmw,
            big_x,
            dotpw_negdotmw,
            big_x_expand,
            big_x_expand,
        ],
    );
    let sum_expand = cadd(d, p, dotpw_negdotmw, dotpw_negdotmw);
    let big_x_x = cadd(d, p, big_x, big_x);

    // reassociate.
    let swap = add_middle_swap_proof(d, p, dot_pw, neg_dot_mw, dot_pw, neg_dot_mw);
    let dotpw_dotpw = cadd(d, p, dot_pw, dot_pw);
    let negdotmw_negdotmw = cadd(d, p, neg_dot_mw, neg_dot_mw);
    let regrouped = cadd(d, p, dotpw_dotpw, negdotmw_negdotmw);

    // dotpw_dotpw ~ mul two dot_pw.
    let two = d.kernel().const_(p.two, vec![]);
    let two_dotpw = cmul(d, p, two, dot_pw);
    let tmed = two_mul_eq_double_proof(d, p, dot_pw); // Equiv(two_dotpw, dotpw_dotpw)
    let tmed_symm = symm(d, p, two_dotpw, dotpw_dotpw, tmed);

    // negdotmw_negdotmw ~ neg(dot_mw+dot_mw).
    let dotmw_dotmw = cadd(d, p, dot_mw, dot_mw);
    let neg_dotmw_dotmw = cneg(d, p, dotmw_dotmw);
    let na = neg_add_proof(d, p, dot_mw, dot_mw); // Equiv (neg dotmw_dotmw) negdotmw_negdotmw
    let na_symm = symm(d, p, neg_dotmw_dotmw, negdotmw_negdotmw, na);

    let congr_regroup = d.lemma(
        creal.add_congr,
        &[
            dotpw_dotpw,
            two_dotpw,
            negdotmw_negdotmw,
            neg_dotmw_dotmw,
            tmed_symm,
            na_symm,
        ],
    );
    let two_dotpw_negdotmwdotmw = cadd(d, p, two_dotpw, neg_dotmw_dotmw);

    let big_x_x_expand = chain(
        d,
        p,
        big_x_x,
        &[
            (sum_expand, congr_xx),
            (regrouped, swap),
            (two_dotpw_negdotmwdotmw, congr_regroup),
        ],
    );

    let neg_r1 = cneg(d, p, pr1);
    let negr1_r2 = cadd(d, p, neg_r1, pr2);
    let power1 = powerp(d, p, pp, po1, pr1);
    let power2 = powerp(d, p, pp, po2, pr2);
    let neg_power2_top = cneg(d, p, power2);
    let power1_neg_power2 = cadd(d, p, power1, neg_power2_top);
    let bigxx_negr1r2 = cadd(d, p, big_x_x, negr1_r2);

    // bigxx_negr1r2 ~ two_dotpw_negdotmwdotmw + negr1_r2.
    let refl_negr1r2 = refl(d, p, negr1_r2);
    let congr_final = d.lemma(
        creal.add_congr,
        &[
            big_x_x,
            two_dotpw_negdotmwdotmw,
            negr1_r2,
            negr1_r2,
            big_x_x_expand,
            refl_negr1r2,
        ],
    );
    let final_sum = cadd(d, p, two_dotpw_negdotmwdotmw, negr1_r2);

    // reassociate: (A+B)+C ~ A+(B+C), A=two_dotpw, B=neg_dotmw_dotmw, C=negr1_r2.
    let assoc = d.lemma(creal.add_assoc, &[two_dotpw, neg_dotmw_dotmw, negr1_r2]);
    let constant = cadd(d, p, neg_dotmw_dotmw, negr1_r2);
    let final_grouped = cadd(d, p, two_dotpw, constant);

    let full_chain = chain(
        d,
        p,
        power1_neg_power2,
        &[
            (bigxx_negr1r2, main_ident),
            (final_sum, congr_final),
            (final_grouped, assoc),
        ],
    );

    let ty_body = equiv(d, p, power1_neg_power2, final_grouped);
    let ty = {
        let w1 = d.pi_fv(pp_fv, point, ty_body);
        let w2 = d.pi_fv(r2_fv, carrier, w1);
        let w3 = d.pi_fv(r1_fv, carrier, w2);
        let w4 = d.pi_fv(o2_fv, point, w3);
        d.pi_fv(o1_fv, point, w4)
    };
    let value = {
        let w1 = d.lam_fv(pp_fv, point, full_chain);
        let w2 = d.lam_fv(r2_fv, carrier, w1);
        let w3 = d.lam_fv(r1_fv, carrier, w2);
        let w4 = d.lam_fv(o2_fv, point, w3);
        d.lam_fv(o1_fv, point, w4)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_difference_linear,
        uparams: vec![],
        ty,
        value,
    })
}

/// **A common point of two circles has equal power, hence lies on the
/// radical axis.** See [`CPointPrelude::two_circles_meet_on_radical_axis`].
/// Composes [`CPointPrelude::power_zero_iff_on_circle`] (`mpr`, both
/// hypotheses) with [`CPointPrelude::radical_axis_iff_dot`] (`mp`) — no
/// fresh algebra, only `Iff.mp`/`Iff.mpr` elimination and one `symm`/`chain`.
fn declare_two_circles_meet_on_radical_axis(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let logic = creal.rat.int.logic;
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

    let o1_fv = d.fresh_fvar();
    let po1 = d.kernel().fvar(o1_fv);
    let o2_fv = d.fresh_fvar();
    let po2 = d.kernel().fvar(o2_fv);
    let r1_fv = d.fresh_fvar();
    let pr1 = d.kernel().fvar(r1_fv);
    let r2_fv = d.fresh_fvar();
    let pr2 = d.kernel().fvar(r2_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let on_circle1_ty = d.const_app(p.on_circle, &[pp, po1, pr1]);
    let on_circle2_ty = d.const_app(p.on_circle, &[pp, po2, pr2]);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let power1 = powerp(d, p, pp, po1, pr1);
    let power2 = powerp(d, p, pp, po2, pr2);
    let zero = czero(d, p);
    let power1_zero_ty = equiv(d, p, power1, zero);
    let power2_zero_ty = equiv(d, p, power2, zero);

    // power1 ~ 0, power2 ~ 0, via power_zero_iff_on_circle's mpr.
    let pz1 = d.lemma(p.power_zero_iff_on_circle, &[pp, po1, pr1]);
    let h1_to_zero = d.lemma(logic.iff_mpr, &[power1_zero_ty, on_circle1_ty, pz1, h1]);
    let pz2 = d.lemma(p.power_zero_iff_on_circle, &[pp, po2, pr2]);
    let h2_to_zero = d.lemma(logic.iff_mpr, &[power2_zero_ty, on_circle2_ty, pz2, h2]);

    // power1 ~ power2.
    let h2_zero_symm = symm(d, p, power2, zero, h2_to_zero); // Equiv zero power2
    let power_eq = chain(d, p, power1, &[(zero, h1_to_zero), (power2, h2_zero_symm)]);

    // Apply radical_axis_iff_dot's mp to reach the dot-form membership
    // statement itself.
    let power_iff_ty = equiv(d, p, power1, power2);
    let pm = d.const_app(p.point_midpoint, &[po1, po2]);
    let sub_p_m = psub(d, p, pp, pm);
    let sub_o2_o1 = psub(d, p, po2, po1);
    let dot_lhs = dotp(d, p, sub_p_m, sub_o2_o1);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let neg_pr2 = cneg(d, p, pr2);
    let v = cadd(d, p, pr1, neg_pr2);
    let c = cmul(d, p, inv2, v);
    let dot_stmt = equiv(d, p, dot_lhs, c);

    let ra = d.lemma(p.radical_axis_iff_dot, &[po1, po2, pr1, pr2, pp]);
    let concl = d.lemma(logic.iff_mp, &[power_iff_ty, dot_stmt, ra, power_eq]);

    let ty_body = {
        let inner = d.arrow(on_circle2_ty, dot_stmt);
        d.arrow(on_circle1_ty, inner)
    };
    let ty = {
        let w1 = d.pi_fv(pp_fv, point, ty_body);
        let w2 = d.pi_fv(r2_fv, carrier, w1);
        let w3 = d.pi_fv(r1_fv, carrier, w2);
        let w4 = d.pi_fv(o2_fv, point, w3);
        d.pi_fv(o1_fv, point, w4)
    };
    let value_body = {
        let inner = d.lam_fv(h2_fv, on_circle2_ty, concl);
        d.lam_fv(h1_fv, on_circle1_ty, inner)
    };
    let value = {
        let w1 = d.lam_fv(pp_fv, point, value_body);
        let w2 = d.lam_fv(r2_fv, carrier, w1);
        let w3 = d.lam_fv(r1_fv, carrier, w2);
        let w4 = d.lam_fv(o2_fv, point, w3);
        d.lam_fv(o1_fv, point, w4)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.two_circles_meet_on_radical_axis,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// The nine-point circle (easy half). `N`, the nine-point centre, is never
// registered as a name: it is always written `point_midpoint(O, H')`, `H'`
// built inline exactly as `declare_circumcentre_orthocentre_construction`/
// `declare_euler_line` build it (see those functions' own docs) — this
// section adds no new intermediate-point constant, matching that
// convention. `midpoint_dist_sq_quarter` is the direct precedent for the
// "quarter" scaling identity these theorems reduce to.
//
// The third equidistant pair (`distSq N (midpoint B C) ~ distSq N (midpoint
// C A)`) is not built here: it is the same argument as
// `declare_nine_point_centre_equidistant`, one more `nine_point_radius_*`
// sibling (the `CA`-midpoint case, `keep := B`) plus a third
// `dist_sq_comm`/`circumcentre_third_distance` combination — mechanical, not
// attempted for time.
//
// NOT ATTEMPTED: the feet of the altitudes (the other six of the nine
// points). Every identity above stays in vector/dot-product form — nothing
// here needs "the point where a perpendicular from `A` meets line `BC`" as a
// *constructed* point, only `dot`-orthogonality as a *hypothesis*
// (`orthocentre_identity`, `thales`). A foot-of-perpendicular construction
// would need: (1) a scalar `t` with `foot := lerp B C t` (this file already
// has `lerp`/`lerp_dist_sq`) satisfying `dot (sub A foot) (sub C B) ~ 0`; (2)
// solving that for `t` needs dividing by `distSq B C` (`dot (sub C B) (sub C
// B))`, which is only invertible under a witnessed `PosBound` — i.e. a
// **non-degeneracy hypothesis** (`B ≠ C`, made `CReal.inv`-usable the way
// `NonCollinear` makes `cross A B C` usable), not free the way every
// unconditional identity above is; and (3) the resulting `foot`'s `distSq`
// to the nine-point centre `N` would need re-deriving from scratch — it is
// not a corollary of `nine_point_radius_bc`/`nine_point_radius_ab`, which are
// about the *side midpoints*, an unrelated three of the nine points.
// ============================================================================

/// Given `sv : Equiv diff (mul inv2 other)`, squares both sides and factors
/// the resulting `inv2²` out. Returns `(other_sq, inv2_other_sq, target,
/// proof)` where `other_sq = mul other other`, `inv2_other_sq = mul inv2
/// other_sq`, `target = mul inv2 inv2_other_sq`, and `proof : Equiv (mul diff
/// diff) target`. The same three-step combination
/// ([`sq_scale_proof`]/`mul_congr`) [`declare_midpoint_dist_sq_quarter`]'s
/// own `build_coord` closure runs inline, pulled out so the nine-point radius
/// theorems below can reuse it without re-deriving it.
fn square_and_scale_quarter(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    diff: ExprId,
    other: ExprId,
    sv: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let inv2_other = cmul(d, p, inv2, other);
    let dist_raw = cmul(d, p, diff, diff);
    let sq_congr = d.lemma(
        creal.mul_congr,
        &[diff, inv2_other, diff, inv2_other, sv, sv],
    );
    let sq_raw = cmul(d, p, inv2_other, inv2_other);
    let sqscale = sq_scale_proof(d, p, inv2, other); // Equiv(sq_raw, inv2*(inv2*(other*other)))
    let other_sq = cmul(d, p, other, other);
    let inv2_other_sq = cmul(d, p, inv2, other_sq);
    let target = cmul(d, p, inv2, inv2_other_sq);
    let dist_total = chain(d, p, dist_raw, &[(sq_raw, sq_congr), (target, sqscale)]);
    (other_sq, inv2_other_sq, target, dist_total)
}

/// Combines two [`square_and_scale_quarter`] results (one per coordinate)
/// into `Equiv (add (mul diffx diffx) (mul diffy diffy)) (mul inv2 (mul inv2
/// (add (mul otherx otherx) (mul othery othery))))` — `distSq(diff) ~
/// inv2·inv2·distSq(other)`. Mirrors
/// [`declare_midpoint_dist_sq_quarter`]'s own two-coordinate combination
/// (`left_distrib` twice, reversed) verbatim.
fn quarter_dist_sq_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    diffx: ExprId,
    diffy: ExprId,
    otherx: ExprId,
    othery: ExprId,
    svx: ExprId,
    svy: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let (xsq, inv2_xsq, target_x, dist_x_total) =
        square_and_scale_quarter(d, p, diffx, otherx, svx);
    let (ysq, inv2_ysq, target_y, dist_y_total) =
        square_and_scale_quarter(d, p, diffy, othery, svy);

    let dist_x_raw = cmul(d, p, diffx, diffx);
    let dist_y_raw = cmul(d, p, diffy, diffy);
    let distsq_raw = cadd(d, p, dist_x_raw, dist_y_raw);
    let combined = cadd(d, p, target_x, target_y);
    let sum_congr = d.lemma(
        creal.add_congr,
        &[
            dist_x_raw,
            target_x,
            dist_y_raw,
            target_y,
            dist_x_total,
            dist_y_total,
        ],
    );

    let xsq_ysq = cadd(d, p, xsq, ysq);
    let d1 = d.lemma(creal.left_distrib, &[inv2, xsq, ysq]); // Equiv(inv2*(xsq+ysq), inv2*xsq+inv2*ysq)
    let inv2_xsqysq = cmul(d, p, inv2, xsq_ysq);
    let inv2_xsq_inv2_ysq = cadd(d, p, inv2_xsq, inv2_ysq);
    let refl_inv2 = refl(d, p, inv2);
    let d2congr = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, inv2_xsqysq, inv2_xsq_inv2_ysq, refl_inv2, d1],
    );
    let target_full = cmul(d, p, inv2, inv2_xsqysq);
    let mul_inv2_sum = cmul(d, p, inv2, inv2_xsq_inv2_ysq);
    let d2 = d.lemma(creal.left_distrib, &[inv2, inv2_xsq, inv2_ysq]);
    let full_reverse = chain(
        d,
        p,
        target_full,
        &[(mul_inv2_sum, d2congr), (combined, d2)],
    );
    let final_reverse = symm(d, p, target_full, combined, full_reverse);

    let final_proof = chain(
        d,
        p,
        distsq_raw,
        &[(combined, sum_congr), (target_full, final_reverse)],
    );
    (distsq_raw, target_full, final_proof)
}

/// `Equiv (add im (neg mce)) (mul inv2 (add (add a (neg c)) (add b (neg e))))`
/// where `im := mul inv2 (add a b)` (=defeq `midpoint a b`), `mce := mul inv2
/// (add c e)` (=defeq `midpoint c e`) — `midpoint(a,b) − midpoint(c,e) ~
/// inv2·((a−c)+(b−e))`, bilinearity of `midpoint` in raw scalar form. Returns
/// `(lhs, rhs, proof)`.
fn midpoint_diff_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let big_x = cadd(d, p, a, b);
    let big_y = cadd(d, p, c, e);
    let im = cmul(d, p, inv2, big_x);
    let mce = cmul(d, p, inv2, big_y);
    let neg_mce = cneg(d, p, mce);
    let lhs = cadd(d, p, im, neg_mce);

    let neg_big_y = cneg(d, p, big_y);
    let x_minus_y_raw = cadd(d, p, big_x, neg_big_y);
    let mul_inv2_xy = cmul(d, p, inv2, x_minus_y_raw);
    let msr = mul_sub_right_proof(d, p, inv2, big_x, big_y); // Equiv(mul_inv2_xy, lhs)
    let msr_symm = symm(d, p, mul_inv2_xy, lhs, msr); // Equiv(lhs, mul_inv2_xy)

    let neg_y = cneg(d, p, big_y);
    let x_y = cadd(d, p, big_x, neg_y); // == mul_inv2_xy's inner argument

    let neg_c = cneg(d, p, c);
    let neg_e = cneg(d, p, e);
    let neg_c_e = cadd(d, p, neg_c, neg_e);
    let split = neg_add_proof(d, p, c, e); // Equiv(neg_y, neg_c_e)
    let refl_x = refl(d, p, big_x);
    let congr_split = d.lemma(
        creal.add_congr,
        &[big_x, big_x, neg_y, neg_c_e, refl_x, split],
    );
    let mid = cadd(d, p, big_x, neg_c_e);

    let swap = add_middle_swap_proof(d, p, a, b, neg_c, neg_e); // Equiv((a+b)+(neg_c+neg_e), (a+neg_c)+(b+neg_e))
    let a_negc = cadd(d, p, a, neg_c);
    let b_nege = cadd(d, p, b, neg_e);
    let target_inner = cadd(d, p, a_negc, b_nege);

    let x_y_reduce = chain(d, p, x_y, &[(mid, congr_split), (target_inner, swap)]);
    let refl_inv2 = refl(d, p, inv2);
    let mul_congr_step = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, x_y, target_inner, refl_inv2, x_y_reduce],
    );
    let rhs = cmul(d, p, inv2, target_inner);

    let proof = chain(d, p, lhs, &[(mul_inv2_xy, msr_symm), (rhs, mul_congr_step)]);
    (lhs, rhs, proof)
}

/// Builds `[x0, neg x0, x1, neg x1, …, x_{k-1}, neg x_{k-1}, rest...]` and
/// proves its right-associated chain `Equiv`s `build_right_chain(rest)`, by
/// `xs.len()` cascaded [`reduce3`] cancellations from the front — each
/// `reduce3(x, x, z, refl x)` peels off one `(x, neg x)` pair, leaving the
/// tail `z` untouched, and the tail becomes the next pair's own chain.
/// Returns `(to_leaves, proof)`.
fn cancelling_pairs_then(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    xs: &[ExprId],
    rest: &[ExprId],
) -> (Vec<ExprId>, ExprId) {
    let mut to_leaves = Vec::new();
    for &x in xs {
        to_leaves.push(x);
        to_leaves.push(cneg(d, p, x));
    }
    to_leaves.extend_from_slice(rest);
    let full = build_right_chain(d, p, &to_leaves);
    let mut steps = Vec::new();
    for (i, &x) in xs.iter().enumerate() {
        let tail = &to_leaves[2 * i + 2..];
        let z = build_right_chain(d, p, tail);
        let refl_x = refl(d, p, x);
        let step = reduce3(d, p, x, x, z, refl_x);
        steps.push((z, step));
    }
    let proof = chain(d, p, full, &steps);
    (to_leaves, proof)
}

/// `Equiv (add (add ox (neg kj)) (add (add keep (neg ox)) (add kj (neg ox))))
///        (add keep (neg ox))` — `(ox−kj) + ((keep−ox)+(kj−ox)) ~ keep−ox`,
/// pure ring algebra in three opaque terms. Returns `(lhs, rhs, proof)`.
fn side_midpoint_cancel_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    ox: ExprId,
    keep: ExprId,
    kj: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let neg_kj = cneg(d, p, kj);
    let neg_ox = cneg(d, p, ox);
    let u = cadd(d, p, ox, neg_kj);
    let keep_negox = cadd(d, p, keep, neg_ox);
    let kj_negox = cadd(d, p, kj, neg_ox);
    let vw = cadd(d, p, keep_negox, kj_negox);
    let lhs = cadd(d, p, u, vw);

    let tree = sadd(
        sadd(SumTree::Leaf(ox), SumTree::Leaf(neg_kj)),
        sadd(
            sadd(SumTree::Leaf(keep), SumTree::Leaf(neg_ox)),
            sadd(SumTree::Leaf(kj), SumTree::Leaf(neg_ox)),
        ),
    );
    let (chain_from, flatten_proof) = flatten_sum_tree(d, p, &tree);
    let mut from_leaves = Vec::new();
    sum_tree_leaves(&tree, &mut from_leaves);

    let (to_leaves, cancel_proof) = cancelling_pairs_then(d, p, &[ox, kj], &[keep, neg_ox]);
    let reorder_proof = reorder_right_chain(d, p, &from_leaves, &to_leaves);
    let chain_to = build_right_chain(d, p, &to_leaves);

    let rhs = cadd(d, p, keep, neg_ox);
    let proof = chain(
        d,
        p,
        lhs,
        &[
            (chain_from, flatten_proof),
            (chain_to, reorder_proof),
            (rhs, cancel_proof),
        ],
    );
    (lhs, rhs, proof)
}

/// The per-coordinate content behind [`CPointPrelude::nine_point_radius_bc`]/
/// [`CPointPrelude::nine_point_radius_ab`]: `N − midpoint(kj,kk) ~
/// inv2·(keep−o)`, where `N`'s coordinate is `midpoint(o, hprime)`, `hprime :=
/// (t1+t2+t3) − (o+o)` (the same construction
/// `declare_circumcentre_orthocentre_construction`/`declare_euler_line` build,
/// here in raw scalar form), and `{keep, kj, kk}` is `{t1, t2, t3}` in some
/// order (`kk` is the vertex `h_prime_minus_vertex_scalar_proof` drops).
/// Returns `(diff, other, proof)` with `proof : Equiv diff (mul inv2 other)`
/// — the exact shape [`square_and_scale_quarter`] consumes as `sv`.
fn n_minus_side_midpoint_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    t1: ExprId,
    t2: ExprId,
    t3: ExprId,
    o: ExprId,
    keep: ExprId,
    kj: ExprId,
    kk: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let creal = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);

    // hprime = (t1+t2+t3) - (o+o), matching
    // `declare_circumcentre_orthocentre_construction`/`declare_euler_line`.
    let t1_t2 = cadd(d, p, t1, t2);
    let s3 = cadd(d, p, t1_t2, t3);
    let oo = cadd(d, p, o, o);
    let neg_oo = cneg(d, p, oo);
    let hprime = cadd(d, p, s3, neg_oo);

    // diff := n - midpoint(kj,kk) ~ inv2*((o-kj)+(hprime-kk))
    let (lhs0, rhs0, proof0) = midpoint_diff_scalar_proof(d, p, o, hprime, kj, kk);

    // hprime - kk ~ (keep-o)+(kj-o), reusing `h_prime_minus_vertex_scalar_proof`
    // unchanged (it needs `kk` to be one of `t1,t2,t3` literally).
    let (hmv_lhs, hmv_rhs, hmv_proof) =
        h_prime_minus_vertex_scalar_proof(d, p, t1, t2, t3, o, kk, keep, kj);

    let neg_kj = cneg(d, p, kj);
    let o_kj = cadd(d, p, o, neg_kj);
    let refl_okj = refl(d, p, o_kj);
    let congr_inner = d.lemma(
        creal.add_congr,
        &[o_kj, o_kj, hmv_lhs, hmv_rhs, refl_okj, hmv_proof],
    ); // Equiv(inner1, inner2)
    let inner1 = cadd(d, p, o_kj, hmv_lhs);
    let inner2 = cadd(d, p, o_kj, hmv_rhs);
    let refl_inv2a = refl(d, p, inv2);
    let congr_mul1 = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, inner1, inner2, refl_inv2a, congr_inner],
    ); // Equiv(rhs0, mul inv2 inner2)
    let mul_inv2_inner2 = cmul(d, p, inv2, inner2);

    let (sc_lhs, sc_rhs, sc_proof) = side_midpoint_cancel_scalar_proof(d, p, o, keep, kj);
    // sc_lhs == inner2 by construction.
    let refl_inv2b = refl(d, p, inv2);
    let congr_mul2 = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, sc_lhs, sc_rhs, refl_inv2b, sc_proof],
    );
    let final_rhs = cmul(d, p, inv2, sc_rhs);

    let proof = chain(
        d,
        p,
        lhs0,
        &[
            (rhs0, proof0),
            (mul_inv2_inner2, congr_mul1),
            (final_rhs, congr_mul2),
        ],
    );
    (lhs0, sc_rhs, proof)
}

/// **The nine-point centre lies on the (additive) Euler line.** See
/// [`CPointPrelude::nine_point_centre_on_euler_line`].
fn declare_nine_point_centre_on_euler_line(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;
    let two = d.kernel().const_(p.two, vec![]);

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
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
    let ox = d.const_app(p.x, &[po]);
    let oy = d.const_app(p.y, &[po]);

    // Point-level `H' := A+B+C-2O`, `N := midpoint O H'`; neither gets a
    // registered name (see the module note above).
    let sum_ab = padd(d, p, pa, pb);
    let sum_abc = padd(d, p, sum_ab, pc);
    let two_o = padd(d, p, po, po);
    let h_prime = psub(d, p, sum_abc, two_o);
    let n_point = d.const_app(p.point_midpoint, &[po, h_prime]);
    let nn = padd(d, p, n_point, n_point);
    let nn_o = padd(d, p, nn, po);

    let big_g = d.const_app(p.centroid, &[pa, pb, pc]);
    let gg = padd(d, p, big_g, big_g);
    let ggg = padd(d, p, gg, big_g);

    let fact_euler = d.lemma(p.euler_line, &[po, pa, pb, pc]); // CPoint.Equiv(H'+2O, ggg)

    let build_coord = |d: &mut IntDev<'_>, ov: ExprId, av: ExprId, bv: ExprId, cv: ExprId| {
        let t1_t2 = cadd(d, p, av, bv);
        let s3 = cadd(d, p, t1_t2, cv);
        let oo = cadd(d, p, ov, ov);
        let neg_oo = cneg(d, p, oo);
        let hprime_v = cadd(d, p, s3, neg_oo);

        let n_v = midpoint(d, p, ov, hprime_v); // == x(N)/y(N)

        let mul_two_nv = cmul(d, p, two, n_v);
        let dm = double_midpoint_proof(d, p, ov, hprime_v); // Equiv(mul_two_nv, ov+hprime_v)
        let tmed = two_mul_eq_double_proof(d, p, n_v); // Equiv(mul_two_nv, n_v+n_v)
        let nv_nv = cadd(d, p, n_v, n_v);
        let tmed_symm = symm(d, p, mul_two_nv, nv_nv, tmed); // Equiv(nv_nv, mul_two_nv)
        let ov_hprimev = cadd(d, p, ov, hprime_v);
        let dm2 = chain(d, p, nv_nv, &[(mul_two_nv, tmed_symm), (ov_hprimev, dm)]);

        let nvnv_ov = cadd(d, p, nv_nv, ov);
        let refl_ov = refl(d, p, ov);
        let congr1 = d.lemma(creal.add_congr, &[nv_nv, ov_hprimev, ov, ov, dm2, refl_ov]);
        let ovhv_ov = cadd(d, p, ov_hprimev, ov);

        let assoc1 = d.lemma(creal.add_assoc, &[ov, hprime_v, ov]); // Equiv(ovhv_ov, ov+(hprimev+ov))
        let hprimev_ov = cadd(d, p, hprime_v, ov);
        let ov_hpov = cadd(d, p, ov, hprimev_ov);

        let comm_inner = d.lemma(creal.add_comm, &[hprime_v, ov]); // Equiv(hprimev_ov, ov+hprimev)
        let refl_ov2 = refl(d, p, ov);
        let ov_hprimev2 = cadd(d, p, ov, hprime_v);
        let congr2 = d.lemma(
            creal.add_congr,
            &[ov, ov, hprimev_ov, ov_hprimev2, refl_ov2, comm_inner],
        );
        let ov_ovhv = cadd(d, p, ov, ov_hprimev2);

        let oo2 = cadd(d, p, ov, ov);
        let assoc2 = d.lemma(creal.add_assoc, &[ov, ov, hprime_v]); // Equiv(oo2+hprimev, ov+(ov+hprimev))
        let oo2_hv = cadd(d, p, oo2, hprime_v);
        let assoc2_symm = symm(d, p, oo2_hv, ov_ovhv, assoc2);

        let comm_outer = d.lemma(creal.add_comm, &[oo2, hprime_v]); // Equiv(oo2_hv, hprimev+oo2)
        let hv_oo2 = cadd(d, p, hprime_v, oo2);

        let final_proof = chain(
            d,
            p,
            nvnv_ov,
            &[
                (ovhv_ov, congr1),
                (ov_hpov, assoc1),
                (ov_ovhv, congr2),
                (oo2_hv, assoc2_symm),
                (hv_oo2, comm_outer),
            ],
        );
        (nvnv_ov, hv_oo2, final_proof)
    };

    let (lhs_x, rhs_x, proof_x) = build_coord(d, ox, ax, bx, cx);
    let (lhs_y, rhs_y, proof_y) = build_coord(d, oy, ay, by, cy);

    let gx = ccentroid_raw(d, p, ax, bx, cx);
    let gy = ccentroid_raw(d, p, ay, by, cy);
    let gxgx = cadd(d, p, gx, gx);
    let gxgx_gx = cadd(d, p, gxgx, gx);
    let gygy = cadd(d, p, gy, gy);
    let gygy_gy = cadd(d, p, gygy, gy);

    let claim_euler_x = equiv(d, p, rhs_x, gxgx_gx);
    let claim_euler_y = equiv(d, p, rhs_y, gygy_gy);
    let euler_x = d.and_left(claim_euler_x, claim_euler_y, fact_euler);
    let euler_y = d.and_right(claim_euler_x, claim_euler_y, fact_euler);

    let final_x = chain(d, p, lhs_x, &[(rhs_x, proof_x), (gxgx_gx, euler_x)]);
    let final_y = chain(d, p, lhs_y, &[(rhs_y, proof_y), (gygy_gy, euler_y)]);

    let claim_x = equiv(d, p, lhs_x, gxgx_gx);
    let claim_y = equiv(d, p, lhs_y, gygy_gy);
    let proof = and_intro(d, p, claim_x, claim_y, final_x, final_y);

    let ty_body = d.const_app(p.point_equiv, &[nn_o, ggg]);
    let ty = {
        let w3 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w3);
        let w1 = d.pi_fv(a_fv, point, w2);
        d.pi_fv(o_fv, point, w1)
    };
    let value = {
        let w3 = d.lam_fv(c_fv, point, proof);
        let w2 = d.lam_fv(b_fv, point, w3);
        let w1 = d.lam_fv(a_fv, point, w2);
        d.lam_fv(o_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.nine_point_centre_on_euler_line,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The nine-point radius relation, `BC`-midpoint case.** See
/// [`CPointPrelude::nine_point_radius_bc`].
fn declare_nine_point_radius_bc(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
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
    let ox = d.const_app(p.x, &[po]);
    let oy = d.const_app(p.y, &[po]);

    let (diffx, otherx, svx) = n_minus_side_midpoint_scalar_proof(d, p, ax, bx, cx, ox, ax, bx, cx);
    let (diffy, othery, svy) = n_minus_side_midpoint_scalar_proof(d, p, ay, by, cy, oy, ay, by, cy);

    let (_distsq_raw, _target_full, final_proof) =
        quarter_dist_sq_proof(d, p, diffx, diffy, otherx, othery, svx, svy);

    let sum_ab = padd(d, p, pa, pb);
    let sum_abc = padd(d, p, sum_ab, pc);
    let two_o = padd(d, p, po, po);
    let h_prime = psub(d, p, sum_abc, two_o);
    let n_point = d.const_app(p.point_midpoint, &[po, h_prime]);
    let m_a = d.const_app(p.point_midpoint, &[pb, pc]);
    let dsq_n_ma = d.const_app(p.dist_sq, &[n_point, m_a]);
    let dsq_a_o = d.const_app(p.dist_sq, &[pa, po]);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let inv2_dsq_ao = cmul(d, p, inv2, dsq_a_o);
    let rhs_nice = cmul(d, p, inv2, inv2_dsq_ao);

    let ty_body = equiv(d, p, dsq_n_ma, rhs_nice);
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
        name: p.nine_point_radius_bc,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The nine-point radius relation, `AB`-midpoint case.** See
/// [`CPointPrelude::nine_point_radius_ab`].
fn declare_nine_point_radius_ab(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
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
    let ox = d.const_app(p.x, &[po]);
    let oy = d.const_app(p.y, &[po]);

    let (diffx, otherx, svx) = n_minus_side_midpoint_scalar_proof(d, p, ax, bx, cx, ox, cx, ax, bx);
    let (diffy, othery, svy) = n_minus_side_midpoint_scalar_proof(d, p, ay, by, cy, oy, cy, ay, by);

    let (_distsq_raw, _target_full, final_proof) =
        quarter_dist_sq_proof(d, p, diffx, diffy, otherx, othery, svx, svy);

    let sum_ab = padd(d, p, pa, pb);
    let sum_abc = padd(d, p, sum_ab, pc);
    let two_o = padd(d, p, po, po);
    let h_prime = psub(d, p, sum_abc, two_o);
    let n_point = d.const_app(p.point_midpoint, &[po, h_prime]);
    let m_c = d.const_app(p.point_midpoint, &[pa, pb]);
    let dsq_n_mc = d.const_app(p.dist_sq, &[n_point, m_c]);
    let dsq_c_o = d.const_app(p.dist_sq, &[pc, po]);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let inv2_dsq_co = cmul(d, p, inv2, dsq_c_o);
    let rhs_nice = cmul(d, p, inv2, inv2_dsq_co);

    let ty_body = equiv(d, p, dsq_n_mc, rhs_nice);
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
        name: p.nine_point_radius_ab,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The nine-point circle's easy half, the headline.** See
/// [`CPointPrelude::nine_point_centre_equidistant`].
fn declare_nine_point_centre_equidistant(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let dsq_oa = d.const_app(p.dist_sq, &[po, pa]);
    let dsq_ob = d.const_app(p.dist_sq, &[po, pb]);
    let dsq_oc = d.const_app(p.dist_sq, &[po, pc]);
    let h1_ty = equiv(d, p, dsq_oa, dsq_ob);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = equiv(d, p, dsq_ob, dsq_oc);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let h13 = d.lemma(p.circumcentre_third_distance, &[po, pa, pb, pc, h1, h2]); // Equiv(dsq_oa, dsq_oc)
    let dsq_ao = d.const_app(p.dist_sq, &[pa, po]);
    let dsq_co = d.const_app(p.dist_sq, &[pc, po]);
    let comm_a = d.lemma(p.dist_sq_comm, &[pa, po]); // Equiv(dsq_ao, dsq_oa)
    let comm_oc = d.lemma(p.dist_sq_comm, &[po, pc]); // Equiv(dsq_oc, dsq_co)
    let ao_eq_co = chain(
        d,
        p,
        dsq_ao,
        &[(dsq_oa, comm_a), (dsq_oc, h13), (dsq_co, comm_oc)],
    );

    let ra = d.lemma(p.nine_point_radius_ab, &[po, pa, pb, pc]); // Equiv(dsq_n_mc, inv2*inv2*dsq_co)
    let rb = d.lemma(p.nine_point_radius_bc, &[po, pa, pb, pc]); // Equiv(dsq_n_ma, inv2*inv2*dsq_ao)

    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let inv2_dsq_co = cmul(d, p, inv2, dsq_co);
    let rhs_c = cmul(d, p, inv2, inv2_dsq_co);
    let inv2_dsq_ao = cmul(d, p, inv2, dsq_ao);
    let rhs_a = cmul(d, p, inv2, inv2_dsq_ao);

    let refl_inv2a = refl(d, p, inv2);
    let inv2_ao_eq_co = d.lemma(
        p.creal.mul_congr,
        &[inv2, inv2, dsq_ao, dsq_co, refl_inv2a, ao_eq_co],
    ); // Equiv(inv2_dsq_ao, inv2_dsq_co)
    let refl_inv2b = refl(d, p, inv2);
    let rhs_a_eq_c = d.lemma(
        p.creal.mul_congr,
        &[
            inv2,
            inv2,
            inv2_dsq_ao,
            inv2_dsq_co,
            refl_inv2b,
            inv2_ao_eq_co,
        ],
    ); // Equiv(rhs_a, rhs_c)

    let sum_ab = padd(d, p, pa, pb);
    let sum_abc = padd(d, p, sum_ab, pc);
    let two_o = padd(d, p, po, po);
    let h_prime = psub(d, p, sum_abc, two_o);
    let n_point = d.const_app(p.point_midpoint, &[po, h_prime]);
    let m_a = d.const_app(p.point_midpoint, &[pb, pc]);
    let m_c = d.const_app(p.point_midpoint, &[pa, pb]);
    let dsq_n_ma = d.const_app(p.dist_sq, &[n_point, m_a]);
    let dsq_n_mc = d.const_app(p.dist_sq, &[n_point, m_c]);

    let rhs_c_to_a = symm(d, p, rhs_a, rhs_c, rhs_a_eq_c); // Equiv(rhs_c, rhs_a)
    let rb_symm = symm(d, p, dsq_n_ma, rhs_a, rb); // Equiv(rhs_a, dsq_n_ma)
    let final_proof = chain(
        d,
        p,
        dsq_n_mc,
        &[(rhs_c, ra), (rhs_a, rhs_c_to_a), (dsq_n_ma, rb_symm)],
    );

    let concl_ty = equiv(d, p, dsq_n_mc, dsq_n_ma);
    let ty_body = {
        let inner = d.arrow(h2_ty, concl_ty);
        d.arrow(h1_ty, inner)
    };
    let ty = {
        let w4 = d.pi_fv(c_fv, point, ty_body);
        let w3 = d.pi_fv(b_fv, point, w4);
        let w2 = d.pi_fv(a_fv, point, w3);
        d.pi_fv(o_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h2_fv, h2_ty, final_proof);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, inner);
        let w4 = d.lam_fv(c_fv, point, with_h1);
        let w3 = d.lam_fv(b_fv, point, w4);
        let w2 = d.lam_fv(a_fv, point, w3);
        d.lam_fv(o_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.nine_point_centre_equidistant,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// Local commutative-ring calculus over CReal, ported from `complex/ring.rs`
// (functions `rn_*`, types `Rn*`). That module is `pub(crate)` but declared
// via a private `mod ring;` inside `complex.rs`, so it is not reachable from
// here without editing `complex.rs` -- off limits for this lane. `ring_proof`
// and its support have zero `ComplexPrelude` dependency (they take
// `CRealPrelude` directly, see that file's own doc comment), so this is a
// mechanical copy with every identifier prefixed `Rn`/`rn_` to avoid
// colliding with this file's own `cadd`/`cmul`/`cneg`/`czero`
// (CPointPrelude-typed, a different signature for the same names). Used by
// the Ceva concurrency proofs below to discharge the underlying polynomial
// identities in `a, b, c, p, q, r` and the cevian-parameter inverse
// mechanically, rather than by a hand-composed `add_comm`/`add_assoc`/
// `mul_comm`/`mul_assoc`/`left_distrib` chain (those identities have too many
// monomials across too many variables for a hand chain to be a safe bet).
// Consider promoting `complex::ring` to a shared, crate-visible module
// instead of this duplication, next time nobody else is mid-edit on
// `complex.rs`.
// ============================================================================

// --- the raw CReal operations ------------------------------------------------

/// `CReal.add a b`.
pub(crate) fn rn_cadd(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.add, &[a, b])
}

/// `CReal.mul a b`.
pub(crate) fn rn_cmul(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.mul, &[a, b])
}

/// `CReal.neg a`.
pub(crate) fn rn_cneg(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(p.neg, &[a])
}

/// `CReal.zero`.
pub(crate) fn rn_czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `CReal.one`.
pub(crate) fn rn_cone(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.one, vec![])
}

/// The proposition `CReal.Equiv a b`. Unused by the Ceva proofs below (which
/// only ever need `rn_ring_proof`'s own `Equiv` conclusion), kept for
/// fidelity with the ported `complex/ring.rs` source (see the module
/// banner) rather than trimmed to only what is currently called.
#[allow(dead_code)]
pub(crate) fn rn_ceq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.equiv, &[a, b])
}

/// `CReal.Equiv.refl a`.
pub(crate) fn rn_crefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

/// `CReal.Equiv.symm`.
pub(crate) fn rn_csymm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// `CReal.Equiv.trans`.
pub(crate) fn rn_ctrans(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    first: ExprId,
    second: ExprId,
) -> ExprId {
    d.lemma(p.equiv_trans, &[a, b, c, first, second])
}

/// Fold a chain of `Equiv` steps from `start`, returning the endpoint and the
/// composite proof. The mirror of `rchain` at `CReal.Equiv`.
pub(crate) fn rn_cchain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> (ExprId, ExprId) {
    let mut current = start;
    let mut proof = rn_crefl(d, p, start);
    for &(next, step) in steps {
        proof = rn_ctrans(d, p, start, current, next, proof, step);
        current = next;
    }
    (current, proof)
}

// --- the two commutative monoids, as one ------------------------------------

/// Which commutative monoid a rn_fold is over.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum RnOp {
    /// `CReal.add`, unit `CReal.zero`.
    Add,
    /// `CReal.mul`, unit `CReal.one`.
    Mul,
}

fn rn_op_term(d: &mut IntDev<'_>, p: CRealPrelude, op: RnOp, a: ExprId, b: ExprId) -> ExprId {
    match op {
        RnOp::Add => rn_cadd(d, p, a, b),
        RnOp::Mul => rn_cmul(d, p, a, b),
    }
}

fn rn_op_unit(d: &mut IntDev<'_>, p: CRealPrelude, op: RnOp) -> ExprId {
    match op {
        RnOp::Add => rn_czero(d, p),
        RnOp::Mul => rn_cone(d, p),
    }
}

/// `Equiv (op a b) (op b a)`.
fn rn_op_comm(d: &mut IntDev<'_>, p: CRealPrelude, op: RnOp, a: ExprId, b: ExprId) -> ExprId {
    let name = match op {
        RnOp::Add => p.add_comm,
        RnOp::Mul => p.mul_comm,
    };
    d.lemma(name, &[a, b])
}

/// `Equiv (op (op a b) c) (op a (op b c))`.
fn rn_op_assoc(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    op: RnOp,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let name = match op {
        RnOp::Add => p.add_assoc,
        RnOp::Mul => p.mul_assoc,
    };
    d.lemma(name, &[a, b, c])
}

/// `Equiv a a' → Equiv b b' → Equiv (op a b) (op a' b')`.
fn rn_op_congr(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    op: RnOp,
    a: ExprId,
    a2: ExprId,
    b: ExprId,
    b2: ExprId,
    left: ExprId,
    right: ExprId,
) -> ExprId {
    let name = match op {
        RnOp::Add => p.add_congr,
        RnOp::Mul => p.mul_congr,
    };
    d.lemma(name, &[a, a2, b, b2, left, right])
}

/// `Equiv (op a unit) a` — `add_zero` / `mul_one`.
fn rn_op_unit_right(d: &mut IntDev<'_>, p: CRealPrelude, op: RnOp, a: ExprId) -> ExprId {
    let name = match op {
        RnOp::Add => p.add_zero,
        RnOp::Mul => p.mul_one,
    };
    d.lemma(name, &[a])
}

/// `Equiv (op unit a) a` — one `comm` away from [`rn_op_unit_right`], and the
/// orientation neither package states.
fn rn_op_unit_left(d: &mut IntDev<'_>, p: CRealPrelude, op: RnOp, a: ExprId) -> ExprId {
    let unit = rn_op_unit(d, p, op);
    let flipped = rn_op_term(d, p, op, a, unit);
    let start = rn_op_term(d, p, op, unit, a);
    let commute = rn_op_comm(d, p, op, unit, a);
    let collapse = rn_op_unit_right(d, p, op, a);
    rn_ctrans(d, p, start, flipped, a, commute, collapse)
}

/// `a0 op (a1 op (… op a_{n-1}))`, right-nested, with the **unit** for the
/// empty list.
pub(crate) fn rn_fold(d: &mut IntDev<'_>, p: CRealPrelude, op: RnOp, atoms: &[ExprId]) -> ExprId {
    let Some((&last, front)) = atoms.split_last() else {
        return rn_op_unit(d, p, op);
    };
    let mut acc = last;
    for &atom in front.iter().rev() {
        acc = rn_op_term(d, p, op, atom, acc);
    }
    acc
}

/// `Equiv (op (rn_fold xs) (rn_fold ys)) (rn_fold (xs ++ ys))`.
fn rn_fold_append(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    op: RnOp,
    xs: &[ExprId],
    ys: &[ExprId],
) -> ExprId {
    if xs.is_empty() {
        let right = rn_fold(d, p, op, ys);
        return rn_op_unit_left(d, p, op, right);
    }
    if ys.is_empty() {
        let left = rn_fold(d, p, op, xs);
        return rn_op_unit_right(d, p, op, left);
    }
    if xs.len() == 1 {
        // `op xs[0] (rn_fold ys)` IS `rn_fold (xs ++ ys)`, syntactically.
        let whole = rn_fold(d, p, op, ys);
        let joined = rn_op_term(d, p, op, xs[0], whole);
        return rn_crefl(d, p, joined);
    }
    let head = xs[0];
    let rest = &xs[1..];
    let rest_fold = rn_fold(d, p, op, rest);
    let ys_fold = rn_fold(d, p, op, ys);
    let start = {
        let left = rn_op_term(d, p, op, head, rest_fold);
        rn_op_term(d, p, op, left, ys_fold)
    };
    let regrouped = {
        let inner = rn_op_term(d, p, op, rest_fold, ys_fold);
        rn_op_term(d, p, op, head, inner)
    };
    let assoc = rn_op_assoc(d, p, op, head, rest_fold, ys_fold);
    let mut joined: Vec<ExprId> = rest.to_vec();
    joined.extend_from_slice(ys);
    let joined_fold = rn_fold(d, p, op, &joined);
    let inner_proof = rn_fold_append(d, p, op, rest, ys);
    let inner_start = rn_op_term(d, p, op, rest_fold, ys_fold);
    let head_refl = rn_crefl(d, p, head);
    let lifted = rn_op_congr(
        d,
        p,
        op,
        head,
        head,
        inner_start,
        joined_fold,
        head_refl,
        inner_proof,
    );
    let target = rn_op_term(d, p, op, head, joined_fold);
    rn_ctrans(d, p, start, regrouped, target, assoc, lifted)
}

/// `Equiv (rn_fold xs) (op xs[i] (rn_fold rest))`, `rest` being `xs` without `i`.
///
/// # Panics
///
/// Panics on an empty list or an out-of-range index.
fn rn_fold_pull(d: &mut IntDev<'_>, p: CRealPrelude, op: RnOp, xs: &[ExprId], i: usize) -> ExprId {
    assert!(i < xs.len(), "rn_fold_pull index out of range");
    if xs.len() == 1 {
        // `rn_fold [x]` is `x`; the target writes `op x unit`.
        let whole = xs[0];
        let unit = rn_op_unit(d, p, op);
        let padded = rn_op_term(d, p, op, whole, unit);
        let collapse = rn_op_unit_right(d, p, op, whole);
        return rn_csymm(d, p, padded, whole, collapse);
    }
    if i == 0 {
        let whole = rn_fold(d, p, op, xs);
        return rn_crefl(d, p, whole);
    }
    let head = xs[0];
    let tail = &xs[1..];
    let chosen = xs[i];
    let mut tail_rest: Vec<ExprId> = tail.to_vec();
    tail_rest.remove(i - 1);
    let tail_fold = rn_fold(d, p, op, tail);
    let tail_rest_fold = rn_fold(d, p, op, &tail_rest);
    let inner = rn_fold_pull(d, p, op, tail, i - 1);

    let start = rn_op_term(d, p, op, head, tail_fold);
    let pulled = rn_op_term(d, p, op, chosen, tail_rest_fold);
    let head_refl = rn_crefl(d, p, head);
    let first = rn_op_congr(d, p, op, head, head, tail_fold, pulled, head_refl, inner);
    let nested = rn_op_term(d, p, op, head, pulled);
    let flat_head = rn_op_term(d, p, op, head, chosen);
    let flat = rn_op_term(d, p, op, flat_head, tail_rest_fold);
    let assoc = rn_op_assoc(d, p, op, head, chosen, tail_rest_fold);
    let second = rn_csymm(d, p, flat, nested, assoc);
    let commuted_head = rn_op_term(d, p, op, chosen, head);
    let commute = rn_op_comm(d, p, op, head, chosen);
    let rest_refl = rn_crefl(d, p, tail_rest_fold);
    let third = rn_op_congr(
        d,
        p,
        op,
        flat_head,
        commuted_head,
        tail_rest_fold,
        tail_rest_fold,
        commute,
        rest_refl,
    );
    let commuted = rn_op_term(d, p, op, commuted_head, tail_rest_fold);
    let fourth = rn_op_assoc(d, p, op, chosen, head, tail_rest_fold);
    let regrouped = {
        let inner_sum = rn_op_term(d, p, op, head, tail_rest_fold);
        rn_op_term(d, p, op, chosen, inner_sum)
    };
    let mut steps = vec![
        (nested, first),
        (flat, second),
        (commuted, third),
        (regrouped, fourth),
    ];
    if tail_rest.is_empty() {
        // `rn_fold (head :: [])` is `head`, but the chain has reached
        // `op chosen (op head unit)`.
        let padded = rn_op_term(d, p, op, head, tail_rest_fold);
        let collapse = rn_op_unit_right(d, p, op, head);
        let chosen_refl = rn_crefl(d, p, chosen);
        let trimmed = rn_op_congr(
            d,
            p,
            op,
            chosen,
            chosen,
            padded,
            head,
            chosen_refl,
            collapse,
        );
        let target = rn_op_term(d, p, op, chosen, head);
        steps.push((target, trimmed));
    }
    let (_, proof) = rn_cchain(d, p, start, &steps);
    proof
}

/// `Equiv (rn_fold xs) (rn_fold ys)` when `ys` is a permutation of `xs`.
///
/// # Panics
///
/// Panics if `ys` is not a permutation of `xs`.
pub(crate) fn rn_fold_perm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    op: RnOp,
    xs: &[ExprId],
    ys: &[ExprId],
) -> ExprId {
    assert_eq!(xs.len(), ys.len(), "rn_fold_perm needs equal lengths");
    if xs.is_empty() {
        let unit = rn_op_unit(d, p, op);
        return rn_crefl(d, p, unit);
    }
    if xs.len() == 1 {
        assert_eq!(xs[0], ys[0], "rn_fold_perm was given a non-permutation");
        return rn_crefl(d, p, xs[0]);
    }
    let target = ys[0];
    let position = xs
        .iter()
        .position(|&x| x == target)
        .expect("rn_fold_perm was given a non-permutation");
    let mut rest: Vec<ExprId> = xs.to_vec();
    rest.remove(position);
    let pull = rn_fold_pull(d, p, op, xs, position);
    let rest_fold = rn_fold(d, p, op, &rest);
    let tail_fold = rn_fold(d, p, op, &ys[1..]);
    let inner = rn_fold_perm(d, p, op, &rest, &ys[1..]);
    let head_refl = rn_crefl(d, p, target);
    let lifted = rn_op_congr(
        d, p, op, target, target, rest_fold, tail_fold, head_refl, inner,
    );
    let start = rn_fold(d, p, op, xs);
    let middle = rn_op_term(d, p, op, target, rest_fold);
    let end = rn_op_term(d, p, op, target, tail_fold);
    rn_ctrans(d, p, start, middle, end, pull, lifted)
}

// --- the derived group and ring identities ----------------------------------

/// `Equiv (add zero a) a`.
fn rn_zero_add(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    rn_op_unit_left(d, p, RnOp::Add, a)
}

/// `Equiv (mul zero a) zero`.
fn rn_zero_mul(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let zero = rn_czero(d, p);
    let start = rn_cmul(d, p, zero, a);
    let flipped = rn_cmul(d, p, a, zero);
    let commute = d.lemma(p.mul_comm, &[zero, a]);
    let collapse = d.lemma(p.mul_zero, &[a]);
    rn_ctrans(d, p, start, flipped, zero, commute, collapse)
}

/// `Equiv (add (neg a) a) zero` — the orientation `add_neg` does not state.
fn rn_neg_add_cancel(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let negated = rn_cneg(d, p, a);
    let start = rn_cadd(d, p, negated, a);
    let flipped = rn_cadd(d, p, a, negated);
    let zero = rn_czero(d, p);
    let commute = d.lemma(p.add_comm, &[negated, a]);
    let collapse = d.lemma(p.add_neg, &[a]);
    rn_ctrans(d, p, start, flipped, zero, commute, collapse)
}

/// `Equiv (neg zero) zero`.
fn rn_neg_zero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero = rn_czero(d, p);
    let negated = rn_cneg(d, p, zero);
    let padded = rn_cadd(d, p, zero, negated);
    let expand = rn_zero_add(d, p, negated);
    let back = rn_csymm(d, p, padded, negated, expand);
    let collapse = d.lemma(p.add_neg, &[zero]);
    rn_ctrans(d, p, negated, padded, zero, back, collapse)
}

/// From `Equiv (add a b) zero`, conclude `Equiv (neg a) b` — uniqueness of the
/// additive inverse, and the lever every sign identity below goes through.
fn rn_neg_eq_of_add_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    hypothesis: ExprId,
) -> ExprId {
    let zero = rn_czero(d, p);
    let negated = rn_cneg(d, p, a);
    let sum = rn_cadd(d, p, a, b);

    let padded = rn_cadd(d, p, negated, zero);
    let collapse = d.lemma(p.add_zero, &[negated]);
    let expand = rn_csymm(d, p, padded, negated, collapse);

    let back = rn_csymm(d, p, sum, zero, hypothesis);
    let neg_refl = rn_crefl(d, p, negated);
    let widened = rn_cadd(d, p, negated, sum);
    let step2 = rn_op_congr(d, p, RnOp::Add, negated, negated, zero, sum, neg_refl, back);

    let regrouped = {
        let inner = rn_cadd(d, p, negated, a);
        rn_cadd(d, p, inner, b)
    };
    let assoc = d.lemma(p.add_assoc, &[negated, a, b]);
    let step3 = rn_csymm(d, p, regrouped, widened, assoc);

    let cancel = rn_neg_add_cancel(d, p, a);
    let b_refl = rn_crefl(d, p, b);
    let inner_left = rn_cadd(d, p, negated, a);
    let step4 = rn_op_congr(d, p, RnOp::Add, inner_left, zero, b, b, cancel, b_refl);
    let with_zero = rn_cadd(d, p, zero, b);
    let step5 = rn_zero_add(d, p, b);

    let (_, proof) = rn_cchain(
        d,
        p,
        negated,
        &[
            (padded, expand),
            (widened, step2),
            (regrouped, step3),
            (with_zero, step4),
            (b, step5),
        ],
    );
    proof
}

/// `Equiv (neg (neg a)) a`.
fn rn_neg_neg(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let negated = rn_cneg(d, p, a);
    let cancel = rn_neg_add_cancel(d, p, a);
    rn_neg_eq_of_add_zero(d, p, negated, a, cancel)
}

/// `Equiv (neg (add a b)) (add (neg a) (neg b))`.
fn rn_neg_add(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = rn_cneg(d, p, a);
    let nb = rn_cneg(d, p, b);
    let zero = rn_czero(d, p);

    // `(a + b) + ((−a) + (−b)) ~ 0`, by reassociation into `a + (−a + (b + −b))`.
    let left = rn_cadd(d, p, a, b);
    let right = rn_cadd(d, p, na, nb);
    let start = rn_cadd(d, p, left, right);
    let joined = rn_fold_append(d, p, RnOp::Add, &[a, b], &[na, nb]);
    let listed = rn_fold(d, p, RnOp::Add, &[a, b, na, nb]);
    let sorted = rn_fold(d, p, RnOp::Add, &[a, na, b, nb]);
    let permuted = rn_fold_perm(d, p, RnOp::Add, &[a, b, na, nb], &[a, na, b, nb]);

    let inner_pair = rn_cadd(d, p, b, nb);
    let pair_zero = d.lemma(p.add_neg, &[b]);
    let na_refl = rn_crefl(d, p, na);
    let inner = rn_op_congr(
        d,
        p,
        RnOp::Add,
        na,
        na,
        inner_pair,
        zero,
        na_refl,
        pair_zero,
    );
    let a_refl = rn_crefl(d, p, a);
    let inner_start = rn_cadd(d, p, na, inner_pair);
    let inner_end = rn_cadd(d, p, na, zero);
    let lifted = rn_op_congr(d, p, RnOp::Add, a, a, inner_start, inner_end, a_refl, inner);
    let stage = rn_cadd(d, p, a, inner_end);
    let trim_inner = d.lemma(p.add_zero, &[na]);
    let a_refl2 = rn_crefl(d, p, a);
    let trimmed = rn_op_congr(d, p, RnOp::Add, a, a, inner_end, na, a_refl2, trim_inner);
    let pair = rn_cadd(d, p, a, na);
    let finish = d.lemma(p.add_neg, &[a]);
    let (_, to_zero) = rn_cchain(
        d,
        p,
        start,
        &[
            (listed, joined),
            (sorted, permuted),
            (stage, lifted),
            (pair, trimmed),
            (zero, finish),
        ],
    );
    rn_neg_eq_of_add_zero(d, p, left, right, to_zero)
}

/// `Equiv (mul (add a b) c) (add (mul a c) (mul b c))`.
fn rn_right_distrib(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let sum = rn_cadd(d, p, a, b);
    let start = rn_cmul(d, p, sum, c);
    let flipped = rn_cmul(d, p, c, sum);
    let commute = d.lemma(p.mul_comm, &[sum, c]);
    let ca = rn_cmul(d, p, c, a);
    let cb = rn_cmul(d, p, c, b);
    let expanded = rn_cadd(d, p, ca, cb);
    let distrib = d.lemma(p.left_distrib, &[c, a, b]);
    let ac = rn_cmul(d, p, a, c);
    let bc = rn_cmul(d, p, b, c);
    let target = rn_cadd(d, p, ac, bc);
    let left_swap = d.lemma(p.mul_comm, &[c, a]);
    let right_swap = d.lemma(p.mul_comm, &[c, b]);
    let swapped = rn_op_congr(d, p, RnOp::Add, ca, ac, cb, bc, left_swap, right_swap);
    let (_, proof) = rn_cchain(
        d,
        p,
        start,
        &[(flipped, commute), (expanded, distrib), (target, swapped)],
    );
    proof
}

/// `Equiv (mul (neg a) b) (neg (mul a b))`.
fn rn_neg_mul(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = rn_cneg(d, p, a);
    let ab = rn_cmul(d, p, a, b);
    let nab = rn_cmul(d, p, na, b);
    let zero = rn_czero(d, p);

    let start = rn_cadd(d, p, ab, nab);
    let factored = {
        let inner = rn_cadd(d, p, a, na);
        rn_cmul(d, p, inner, b)
    };
    let expand = rn_right_distrib(d, p, a, na, b);
    let back = rn_csymm(d, p, factored, start, expand);
    let inner_sum = rn_cadd(d, p, a, na);
    let cancel = d.lemma(p.add_neg, &[a]);
    let b_refl = rn_crefl(d, p, b);
    let collapsed = rn_cmul(d, p, zero, b);
    let step = rn_op_congr(d, p, RnOp::Mul, inner_sum, zero, b, b, cancel, b_refl);
    let finish = rn_zero_mul(d, p, b);
    let (_, to_zero) = rn_cchain(
        d,
        p,
        start,
        &[(factored, back), (collapsed, step), (zero, finish)],
    );
    let uniqueness = rn_neg_eq_of_add_zero(d, p, ab, nab, to_zero);
    let negated_product = rn_cneg(d, p, ab);
    rn_csymm(d, p, negated_product, nab, uniqueness)
}

/// `Equiv (mul a (neg b)) (neg (mul a b))`.
fn rn_mul_neg(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nb = rn_cneg(d, p, b);
    let start = rn_cmul(d, p, a, nb);
    let flipped = rn_cmul(d, p, nb, a);
    let commute = d.lemma(p.mul_comm, &[a, nb]);
    let ba = rn_cmul(d, p, b, a);
    let pulled = rn_cneg(d, p, ba);
    let pull = rn_neg_mul(d, p, b, a);
    let ab = rn_cmul(d, p, a, b);
    let target = rn_cneg(d, p, ab);
    let swap = d.lemma(p.mul_comm, &[b, a]);
    let lifted = d.lemma(p.neg_congr, &[ba, ab, swap]);
    let (_, proof) = rn_cchain(
        d,
        p,
        start,
        &[(flipped, commute), (pulled, pull), (target, lifted)],
    );
    proof
}

// --- the normal form ---------------------------------------------------------

/// One signed monomial: a **sorted** list of atoms, and a sign.
///
/// Field order is load-bearing: the derived `Ord` sorts by atoms first, so
/// monomials over the same atoms with opposite signs land adjacent and
/// [`rn_canonicalize`] can cancel them in one pass.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct RnMono {
    atoms: Vec<ExprId>,
    neg: bool,
}

/// A formal expression over `CReal`, in the language the normalizer decides.
///
/// [`RnExpr::Zero`] and [`RnExpr::One`] are the *constants* `CReal.zero` and
/// `CReal.one`, not atoms: the whole point is that `x · 1` and `x · 0` collapse.
#[derive(Clone, Debug)]
pub(crate) enum RnExpr {
    /// An opaque `CReal` term — a variable, or anything the calculus should not
    /// look inside.
    Atom(ExprId),
    /// `CReal.zero`. Unconstructed by the Ceva proofs below (their
    /// correction terms are built from `One`/`Neg`/atoms, never a bare
    /// zero literal), kept for fidelity with the ported source.
    #[allow(dead_code)]
    Zero,
    /// `CReal.one`.
    One,
    /// `CReal.add`.
    Add(Box<RnExpr>, Box<RnExpr>),
    /// `CReal.mul`.
    Mul(Box<RnExpr>, Box<RnExpr>),
    /// `CReal.neg`.
    Neg(Box<RnExpr>),
}

impl RnExpr {
    /// `a + b`.
    pub(crate) fn add(a: RnExpr, b: RnExpr) -> RnExpr {
        RnExpr::Add(Box::new(a), Box::new(b))
    }
    /// `a · b`.
    pub(crate) fn mul(a: RnExpr, b: RnExpr) -> RnExpr {
        RnExpr::Mul(Box::new(a), Box::new(b))
    }
    /// `−a`.
    pub(crate) fn neg(a: RnExpr) -> RnExpr {
        RnExpr::Neg(Box::new(a))
    }
}

/// Render a formal expression as the `CReal` term it denotes.
pub(crate) fn rn_render(d: &mut IntDev<'_>, p: CRealPrelude, e: &RnExpr) -> ExprId {
    match e {
        RnExpr::Atom(a) => *a,
        RnExpr::Zero => rn_czero(d, p),
        RnExpr::One => rn_cone(d, p),
        RnExpr::Add(a, b) => {
            let left = rn_render(d, p, a);
            let right = rn_render(d, p, b);
            rn_cadd(d, p, left, right)
        }
        RnExpr::Mul(a, b) => {
            let left = rn_render(d, p, a);
            let right = rn_render(d, p, b);
            rn_cmul(d, p, left, right)
        }
        RnExpr::Neg(a) => {
            let inner = rn_render(d, p, a);
            rn_cneg(d, p, inner)
        }
    }
}

fn rn_mono_term(d: &mut IntDev<'_>, p: CRealPrelude, m: &RnMono) -> ExprId {
    let product = rn_fold(d, p, RnOp::Mul, &m.atoms);
    if m.neg {
        rn_cneg(d, p, product)
    } else {
        product
    }
}

fn rn_mono_terms(d: &mut IntDev<'_>, p: CRealPrelude, monos: &[RnMono]) -> Vec<ExprId> {
    monos.iter().map(|m| rn_mono_term(d, p, m)).collect()
}

/// The canonical term of a monomial multiset: `zero` when empty.
pub(crate) fn rn_sum_term(d: &mut IntDev<'_>, p: CRealPrelude, monos: &[RnMono]) -> ExprId {
    let terms = rn_mono_terms(d, p, monos);
    rn_fold(d, p, RnOp::Add, &terms)
}

fn rn_flip(monos: &[RnMono]) -> Vec<RnMono> {
    monos
        .iter()
        .map(|m| RnMono {
            atoms: m.atoms.clone(),
            neg: !m.neg,
        })
        .collect()
}

/// `Equiv (neg (rn_sum_term monos)) (rn_sum_term (rn_flip monos))`.
fn rn_neg_sum(d: &mut IntDev<'_>, p: CRealPrelude, monos: &[RnMono]) -> ExprId {
    match monos {
        [] => rn_neg_zero(d, p),
        [m] => {
            let product = rn_fold(d, p, RnOp::Mul, &m.atoms);
            if m.neg {
                // `neg (neg P) ~ P`.
                rn_neg_neg(d, p, product)
            } else {
                // `neg P` is already the flipped monomial's term.
                let negated = rn_cneg(d, p, product);
                rn_crefl(d, p, negated)
            }
        }
        [head, rest @ ..] => {
            let head_term = rn_mono_term(d, p, head);
            let rest_term = rn_sum_term(d, p, rest);
            let split = rn_neg_add(d, p, head_term, rest_term);
            let negated_head = rn_cneg(d, p, head_term);
            let negated_rest = rn_cneg(d, p, rest_term);
            let head_slice = std::slice::from_ref(head);
            let head_proof = rn_neg_sum(d, p, head_slice);
            let rest_proof = rn_neg_sum(d, p, rest);
            let flipped_head = rn_flip(head_slice);
            let flipped_rest = rn_flip(rest);
            let flipped_head_term = rn_sum_term(d, p, &flipped_head);
            let flipped_rest_term = rn_sum_term(d, p, &flipped_rest);
            let lifted = rn_op_congr(
                d,
                p,
                RnOp::Add,
                negated_head,
                flipped_head_term,
                negated_rest,
                flipped_rest_term,
                head_proof,
                rest_proof,
            );
            let joint = rn_cadd(d, p, head_term, rest_term);
            let start = rn_cneg(d, p, joint);
            let middle = rn_cadd(d, p, negated_head, negated_rest);
            let end = rn_cadd(d, p, flipped_head_term, flipped_rest_term);
            rn_ctrans(d, p, start, middle, end, split, lifted)
        }
    }
}

fn rn_mul_mono_mono(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    m: &RnMono,
    n: &RnMono,
) -> (RnMono, ExprId) {
    let mut concat: Vec<ExprId> = m.atoms.clone();
    concat.extend_from_slice(&n.atoms);
    let mut sorted = concat.clone();
    sorted.sort_unstable();
    let result = RnMono {
        atoms: sorted.clone(),
        neg: m.neg != n.neg,
    };

    let left = rn_fold(d, p, RnOp::Mul, &m.atoms);
    let right = rn_fold(d, p, RnOp::Mul, &n.atoms);
    let raw = rn_cmul(d, p, left, right);
    let concat_fold = rn_fold(d, p, RnOp::Mul, &concat);
    let sorted_fold = rn_fold(d, p, RnOp::Mul, &sorted);
    let append = rn_fold_append(d, p, RnOp::Mul, &m.atoms, &n.atoms);
    let permute = rn_fold_perm(d, p, RnOp::Mul, &concat, &sorted);
    let base = rn_ctrans(d, p, raw, concat_fold, sorted_fold, append, permute);

    let proof = match (m.neg, n.neg) {
        (false, false) => base,
        (true, false) => {
            let negated_left = rn_cneg(d, p, left);
            let start = rn_cmul(d, p, negated_left, right);
            let pulled = rn_cneg(d, p, raw);
            let pull = rn_neg_mul(d, p, left, right);
            let target = rn_cneg(d, p, sorted_fold);
            let lifted = d.lemma(p.neg_congr, &[raw, sorted_fold, base]);
            let (_, proof) = rn_cchain(d, p, start, &[(pulled, pull), (target, lifted)]);
            proof
        }
        (false, true) => {
            let negated_right = rn_cneg(d, p, right);
            let start = rn_cmul(d, p, left, negated_right);
            let pulled = rn_cneg(d, p, raw);
            let pull = rn_mul_neg(d, p, left, right);
            let target = rn_cneg(d, p, sorted_fold);
            let lifted = d.lemma(p.neg_congr, &[raw, sorted_fold, base]);
            let (_, proof) = rn_cchain(d, p, start, &[(pulled, pull), (target, lifted)]);
            proof
        }
        (true, true) => {
            let negated_left = rn_cneg(d, p, left);
            let negated_right = rn_cneg(d, p, right);
            let start = rn_cmul(d, p, negated_left, negated_right);
            let inner_start = rn_cmul(d, p, left, negated_right);
            let once = rn_cneg(d, p, inner_start);
            let first = rn_neg_mul(d, p, left, negated_right);
            let inner = rn_mul_neg(d, p, left, right);
            let inner_end = rn_cneg(d, p, raw);
            let second = d.lemma(p.neg_congr, &[inner_start, inner_end, inner]);
            let twice = rn_cneg(d, p, inner_end);
            let third = rn_neg_neg(d, p, raw);
            let (_, proof) = rn_cchain(
                d,
                p,
                start,
                &[
                    (once, first),
                    (twice, second),
                    (raw, third),
                    (sorted_fold, base),
                ],
            );
            proof
        }
    };
    (result, proof)
}

fn rn_mul_mono_sum(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    m: &RnMono,
    ns: &[RnMono],
) -> (Vec<RnMono>, ExprId) {
    let head_term = rn_mono_term(d, p, m);
    match ns {
        [] => {
            let proof = d.lemma(p.mul_zero, &[head_term]);
            (Vec::new(), proof)
        }
        [n] => {
            let (result, proof) = rn_mul_mono_mono(d, p, m, n);
            (vec![result], proof)
        }
        [n, rest @ ..] => {
            let first_term = rn_mono_term(d, p, n);
            let rest_term = rn_sum_term(d, p, rest);
            let sum = rn_cadd(d, p, first_term, rest_term);
            let start = rn_cmul(d, p, head_term, sum);
            let distrib = d.lemma(p.left_distrib, &[head_term, first_term, rest_term]);
            let left_product = rn_cmul(d, p, head_term, first_term);
            let right_product = rn_cmul(d, p, head_term, rest_term);
            let expanded = rn_cadd(d, p, left_product, right_product);

            let (first_result, first_proof) = rn_mul_mono_mono(d, p, m, n);
            let (rest_result, rest_proof) = rn_mul_mono_sum(d, p, m, rest);
            let first_canon = rn_mono_term(d, p, &first_result);
            let rest_canon = rn_sum_term(d, p, &rest_result);
            let lifted = rn_op_congr(
                d,
                p,
                RnOp::Add,
                left_product,
                first_canon,
                right_product,
                rest_canon,
                first_proof,
                rest_proof,
            );
            let paired = rn_cadd(d, p, first_canon, rest_canon);

            let rest_terms = rn_mono_terms(d, p, &rest_result);
            let join = rn_fold_append(d, p, RnOp::Add, &[first_canon], &rest_terms);
            let mut result = vec![first_result];
            result.extend(rest_result);
            let joined = rn_sum_term(d, p, &result);

            let (_, proof) = rn_cchain(
                d,
                p,
                start,
                &[(expanded, distrib), (paired, lifted), (joined, join)],
            );
            (result, proof)
        }
    }
}

fn rn_mul_sum_sum(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    ms: &[RnMono],
    ns: &[RnMono],
) -> (Vec<RnMono>, ExprId) {
    match ms {
        [] => {
            let right = rn_sum_term(d, p, ns);
            let proof = rn_zero_mul(d, p, right);
            (Vec::new(), proof)
        }
        [m] => rn_mul_mono_sum(d, p, m, ns),
        [m, rest @ ..] => {
            let head_term = rn_mono_term(d, p, m);
            let rest_term = rn_sum_term(d, p, rest);
            let right = rn_sum_term(d, p, ns);
            let sum = rn_cadd(d, p, head_term, rest_term);
            let start = rn_cmul(d, p, sum, right);
            let distrib = rn_right_distrib(d, p, head_term, rest_term, right);
            let left_product = rn_cmul(d, p, head_term, right);
            let right_product = rn_cmul(d, p, rest_term, right);
            let expanded = rn_cadd(d, p, left_product, right_product);

            let (first_result, first_proof) = rn_mul_mono_sum(d, p, m, ns);
            let (rest_result, rest_proof) = rn_mul_sum_sum(d, p, rest, ns);
            let first_canon = rn_sum_term(d, p, &first_result);
            let rest_canon = rn_sum_term(d, p, &rest_result);
            let lifted = rn_op_congr(
                d,
                p,
                RnOp::Add,
                left_product,
                first_canon,
                right_product,
                rest_canon,
                first_proof,
                rest_proof,
            );
            let paired = rn_cadd(d, p, first_canon, rest_canon);

            let first_terms = rn_mono_terms(d, p, &first_result);
            let rest_terms = rn_mono_terms(d, p, &rest_result);
            let join = rn_fold_append(d, p, RnOp::Add, &first_terms, &rest_terms);
            let mut result = first_result;
            result.extend(rest_result);
            let joined = rn_sum_term(d, p, &result);

            let (_, proof) = rn_cchain(
                d,
                p,
                start,
                &[(expanded, distrib), (paired, lifted), (joined, join)],
            );
            (result, proof)
        }
    }
}

/// `(normal form, proof of `Equiv (rn_render e) (rn_sum_term normal form)`)`.
fn rn_normalize(d: &mut IntDev<'_>, p: CRealPrelude, e: &RnExpr) -> (Vec<RnMono>, ExprId) {
    match e {
        RnExpr::Atom(a) => {
            let monos = vec![RnMono {
                atoms: vec![*a],
                neg: false,
            }];
            let proof = rn_crefl(d, p, *a);
            (monos, proof)
        }
        RnExpr::Zero => {
            let zero = rn_czero(d, p);
            let proof = rn_crefl(d, p, zero);
            (Vec::new(), proof)
        }
        RnExpr::One => {
            let one = rn_cone(d, p);
            let proof = rn_crefl(d, p, one);
            (
                vec![RnMono {
                    atoms: Vec::new(),
                    neg: false,
                }],
                proof,
            )
        }
        RnExpr::Neg(inner) => {
            let (monos, proof) = rn_normalize(d, p, inner);
            let source = rn_render(d, p, inner);
            let canon = rn_sum_term(d, p, &monos);
            let start = rn_cneg(d, p, source);
            let middle = rn_cneg(d, p, canon);
            let lifted = d.lemma(p.neg_congr, &[source, canon, proof]);
            let flipped = rn_flip(&monos);
            let end = rn_sum_term(d, p, &flipped);
            let distribute = rn_neg_sum(d, p, &monos);
            let composite = rn_ctrans(d, p, start, middle, end, lifted, distribute);
            (flipped, composite)
        }
        RnExpr::Add(a, b) => {
            let (ma, pa) = rn_normalize(d, p, a);
            let (mb, pb) = rn_normalize(d, p, b);
            let source_a = rn_render(d, p, a);
            let source_b = rn_render(d, p, b);
            let canon_a = rn_sum_term(d, p, &ma);
            let canon_b = rn_sum_term(d, p, &mb);
            let start = rn_cadd(d, p, source_a, source_b);
            let middle = rn_cadd(d, p, canon_a, canon_b);
            let lifted = rn_op_congr(
                d,
                p,
                RnOp::Add,
                source_a,
                canon_a,
                source_b,
                canon_b,
                pa,
                pb,
            );
            let terms_a = rn_mono_terms(d, p, &ma);
            let terms_b = rn_mono_terms(d, p, &mb);
            let join = rn_fold_append(d, p, RnOp::Add, &terms_a, &terms_b);
            let mut result = ma;
            result.extend(mb);
            let end = rn_sum_term(d, p, &result);
            let composite = rn_ctrans(d, p, start, middle, end, lifted, join);
            (result, composite)
        }
        RnExpr::Mul(a, b) => {
            let (ma, pa) = rn_normalize(d, p, a);
            let (mb, pb) = rn_normalize(d, p, b);
            let source_a = rn_render(d, p, a);
            let source_b = rn_render(d, p, b);
            let canon_a = rn_sum_term(d, p, &ma);
            let canon_b = rn_sum_term(d, p, &mb);
            let start = rn_cmul(d, p, source_a, source_b);
            let middle = rn_cmul(d, p, canon_a, canon_b);
            let lifted = rn_op_congr(
                d,
                p,
                RnOp::Mul,
                source_a,
                canon_a,
                source_b,
                canon_b,
                pa,
                pb,
            );
            let (result, expand) = rn_mul_sum_sum(d, p, &ma, &mb);
            let end = rn_sum_term(d, p, &result);
            let composite = rn_ctrans(d, p, start, middle, end, lifted, expand);
            (result, composite)
        }
    }
}

/// Sort the multiset and cancel opposite pairs.
///
/// Returns the canonical multiset and a proof that the original sum is
/// `Equiv` to it.
fn rn_canonicalize(d: &mut IntDev<'_>, p: CRealPrelude, monos: &[RnMono]) -> (Vec<RnMono>, ExprId) {
    let mut current: Vec<RnMono> = monos.to_vec();
    let start = rn_sum_term(d, p, &current);
    let mut steps: Vec<(ExprId, ExprId)> = Vec::new();

    // Sort once: the derived `Ord` puts equal-atom monomials adjacent.
    let mut sorted = current.clone();
    sorted.sort();
    if sorted != current {
        let from = rn_mono_terms(d, p, &current);
        let to = rn_mono_terms(d, p, &sorted);
        let permute = rn_fold_perm(d, p, RnOp::Add, &from, &to);
        let target = rn_sum_term(d, p, &sorted);
        steps.push((target, permute));
        current = sorted;
    }

    // Cancel adjacent opposite pairs until none remain. Removing two adjacent
    // entries from a sorted list leaves it sorted, so no re-sort is needed.
    while let Some(index) = (0..current.len().saturating_sub(1))
        .find(|&i| current[i].atoms == current[i + 1].atoms && current[i].neg != current[i + 1].neg)
    {
        let mut reordered = vec![current[index].clone(), current[index + 1].clone()];
        for (position, mono) in current.iter().enumerate() {
            if position != index && position != index + 1 {
                reordered.push(mono.clone());
            }
        }
        let from = rn_mono_terms(d, p, &current);
        let to = rn_mono_terms(d, p, &reordered);
        let permute = rn_fold_perm(d, p, RnOp::Add, &from, &to);
        let moved = rn_sum_term(d, p, &reordered);
        steps.push((moved, permute));

        let first = rn_mono_term(d, p, &reordered[0]);
        let second = rn_mono_term(d, p, &reordered[1]);
        let product = rn_fold(d, p, RnOp::Mul, &reordered[0].atoms);
        let pair_zero = if reordered[0].neg {
            rn_neg_add_cancel(d, p, product)
        } else {
            d.lemma(p.add_neg, &[product])
        };
        let zero = rn_czero(d, p);
        let rest = &reordered[2..];
        let remainder: Vec<RnMono> = rest.to_vec();
        if remainder.is_empty() {
            steps.push((zero, pair_zero));
        } else {
            let rest_term = rn_sum_term(d, p, &remainder);
            let regrouped = {
                let pair = rn_cadd(d, p, first, second);
                rn_cadd(d, p, pair, rest_term)
            };
            let nested = {
                let inner = rn_cadd(d, p, second, rest_term);
                rn_cadd(d, p, first, inner)
            };
            let assoc = d.lemma(p.add_assoc, &[first, second, rest_term]);
            let regroup = rn_csymm(d, p, regrouped, nested, assoc);
            steps.push((regrouped, regroup));

            let pair = rn_cadd(d, p, first, second);
            let rest_refl = rn_crefl(d, p, rest_term);
            let collapsed = rn_cadd(d, p, zero, rest_term);
            let collapse = rn_op_congr(
                d,
                p,
                RnOp::Add,
                pair,
                zero,
                rest_term,
                rest_term,
                pair_zero,
                rest_refl,
            );
            steps.push((collapsed, collapse));
            let trim = rn_zero_add(d, p, rest_term);
            steps.push((rest_term, trim));
        }
        current = remainder;
    }

    let (_, proof) = rn_cchain(d, p, start, &steps);
    (current, proof)
}

/// A proof of `CReal.Equiv (rn_render lhs) (rn_render rhs)`.
///
/// # Panics
///
/// Panics when the two normal forms differ — the identity is **not** a
/// consequence of the commutative-ring laws, and the caller is wrong. The
/// message names both normal forms rather than letting the kernel reject an
/// enormous term with a type mismatch.
pub(crate) fn rn_ring_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    lhs: &RnExpr,
    rhs: &RnExpr,
) -> ExprId {
    let left_source = rn_render(d, p, lhs);
    let right_source = rn_render(d, p, rhs);

    let (raw_left, left_proof) = rn_normalize(d, p, lhs);
    let raw_left_term = rn_sum_term(d, p, &raw_left);
    let (canon_left, left_canon_proof) = rn_canonicalize(d, p, &raw_left);
    let canon_left_term = rn_sum_term(d, p, &canon_left);
    let full_left = rn_ctrans(
        d,
        p,
        left_source,
        raw_left_term,
        canon_left_term,
        left_proof,
        left_canon_proof,
    );

    let (raw_right, right_proof) = rn_normalize(d, p, rhs);
    let raw_right_term = rn_sum_term(d, p, &raw_right);
    let (canon_right, right_canon_proof) = rn_canonicalize(d, p, &raw_right);
    let canon_right_term = rn_sum_term(d, p, &canon_right);
    let full_right = rn_ctrans(
        d,
        p,
        right_source,
        raw_right_term,
        canon_right_term,
        right_proof,
        right_canon_proof,
    );

    assert_eq!(
        canon_left, canon_right,
        "rn_ring_proof: the two sides have different normal forms, so the identity \
         does not follow from the commutative-ring laws"
    );
    let back = rn_csymm(d, p, right_source, canon_right_term, full_right);
    rn_ctrans(
        d,
        p,
        left_source,
        canon_left_term,
        right_source,
        full_left,
        back,
    )
}

// ============================================================================
// Ceva's theorem: cevians AX, BY, CZ (X on BC, Y on CA, Z on AB, each an
// explicit `lerp` affine combination -- see [`CPointPrelude::point_lerp`])
// are concurrent when the ratio product `p*q*r ~ (1-p)*(1-q)*(1-r)` holds
// (the classical `(BX/XC)*(CY/YA)*(AZ/ZB) = 1`, division-free).
//
// ## The construction, on paper
//
// Write `X := lerp B C p`, `Y := lerp C A q`, `Z := lerp A B r`. Barycentric
// bookkeeping (worked with `sympy`, not by hand -- see
// `scripts/`-adjacent session notes) gives the intersection of cevians `AX`
// and `BY` as `lerp A X t ~ lerp B Y u` with
//
//     D := (1 - q) + p*q          -- purely a function of p,q; independent
//                                     of the triangle A,B,C
//     t := (1 - q) * D⁻¹,   u := p * D⁻¹
//
// as a **pure ring identity in the cevian-parameter denominator's inverse**:
// writing `z` for that inverse,
//
//     lerp a (lerp b c p) t  -  lerp b (lerp c a q) u  ~  (D*z - 1) * (b - a)
//
// for EVERY scalar `a,b,c` (this is [`cevian_pair_ax_by_scalar_proof`]'s
// content, discharged by [`rn_ring_proof`] -- the correction term vanishes
// once `z` actually is `D⁻¹`, i.e. once `D*z ~ 1`). Continuing to the third
// cevian `CZ` picks up a SECOND correction term that needs the Ceva ratio
// condition itself:
//
//     lerp b (lerp c a q) u  -  lerp c (lerp a b r) v  ~
//         (D*z - 1)*(c - b)  +  (z*(a - b)) * (p*q*r - (1-p)*(1-q)*(1-r))
//
// with `v := (1 - p - q + 2*p*q) * z`. Both identities were verified exactly
// with `sympy` (polynomial division, then a zero-residual check) before
// being encoded here; `D` and the cofactors are NOT independently
// re-derived by the Lean kernel -- `rn_ring_proof` only checks that both
// sides of each stated identity share a normal form, which is exactly the
// claim the `sympy` check already confirmed.
//
// `D` depends only on `p, q` -- **not** on `A, B, C` -- so the
// non-degeneracy hypothesis every theorem below carries (`PosBound (mul D
// D) k`, the same witnessed-squared idiom [`CPointPrelude::non_collinear`]
// uses) is a fact about the two cevian ratios, not about the triangle.
// Nothing here needs [`CPointPrelude::non_collinear`] at all: two cevians
// with parameters `p, q` fail to meet (as vectors, in ANY affine frame) iff
// `D = 0`, regardless of whether `A, B, C` are themselves collinear.
//
// `z` is built from `D` exactly the way
// [`CPointPrelude::circumcentre_unique`]'s proof consumes
// [`CPointPrelude::non_collinear`]: never inverting `D` directly (its sign
// is unknown), but squaring first (`PosBound (D*D) k` is provable whenever
// `D ≠ 0`, whatever its sign) and using `D * (D*D)⁻¹ = D⁻¹` via one
// `mul_assoc`/`mul_inv_cancel` step ([`cevian_dinv_cancel`]).
//
// ## Why a local ring-normalization port, not hand-composed chains
//
// The two identities above have up to 3 free scalars beyond `a,b,c`
// (`p,q,r,z`) and, expanded, dozens of monomials -- an order of magnitude
// past what this file's existing bespoke `*_scalar_proof` helpers
// (`lagrange_identity_scalar_proof`, `stewart_ring_core_proof`, …) were
// built for. `rn_ring_proof` (ported above from `complex/ring.rs`, see that
// section's banner) is a decision procedure for exactly this: it panics
// loudly if the two normal forms disagree, rather than risking a
// kernel-rejected multi-hundred-node term from a hand mis-association.
//
// ## Matching shapes, not just values: why the `rn_*` trees mirror
// `lerp_raw`/`CPoint.lerp` exactly
//
// Every scalar identity below is proved entirely in terms of `x P`/`y P`
// coordinate projections and raw `CReal` operations; the outer theorems
// state their conclusion using `CPoint.lerp`/`CPoint.Equiv` instead. The
// kernel accepts this because `CReal.Equiv` and defeq are different
// relations: what bridges the gap is that `x (CPoint.lerp P Q t)` DELTA/IOTA
// *reduces* (definitionally, no proof needed) to exactly
// `Scalar.lerp (x P) (x Q) t`, which is [`lerp_raw`]'s own shape. So every
// `RnExpr` tree that stands for a `lerp` below is built with
// [`rn_lerp`] -- the `RnExpr` mirror of [`lerp_raw`] -- never with a
// re-associated or coefficient-expanded equivalent, and every `D`, cevian
// coefficient, or Ceva-defect term that needs to appear identically in more
// than one place (a hypothesis's type and a proof step's input, or the
// same subterm inside two different `RnExpr` trees) is built by calling
// the SAME small `rn_*` constructor function each time and letting the
// kernel's hash-consed expression arena (`Kernel::intern_expr`, structural
// interning -- confirmed by reading `crates/axeyum-lean-kernel/src/lib.rs`)
// guarantee the two calls land on the identical `ExprId`, rather than by
// hand-retyping the same nested `add`/`mul`/`neg` chain twice and hoping
// the parenthesisation matches. `CReal.Equiv` (unlike `=`) is not something
// the kernel's defeq checker reasons about on its own, so a structural
// mismatch here would show up as a rejected proof, not a wrong theorem --
// but a rejected proof on a term this size is exactly the "180s to fail"
// trap the module doc for this whole file warns about, so the point is to
// avoid ever hand-duplicating a subterm's shape in the first place.

/// The `RnExpr` mirror of [`lerp_raw`]: `a + t*(b-a)`, in exactly the shape
/// `x (CPoint.lerp P Q t)` reduces to (`add a (mul t (add b (neg a)))`).
/// Every cevian point built as an `RnExpr` below goes through this, never a
/// re-associated equivalent -- see the module note on why the shapes must
/// match `lerp_raw` exactly, not just be ring-equal to it.
fn rn_lerp(a: RnExpr, b: RnExpr, t: RnExpr) -> RnExpr {
    RnExpr::add(a.clone(), RnExpr::mul(t, RnExpr::add(b, RnExpr::neg(a))))
}

/// The `RnExpr` for `x - y`.
fn rn_diff(x: RnExpr, y: RnExpr) -> RnExpr {
    RnExpr::add(x, RnExpr::neg(y))
}

/// The `RnExpr` for `1 - x`.
fn rn_one_minus(x: RnExpr) -> RnExpr {
    RnExpr::add(RnExpr::One, RnExpr::neg(x))
}

/// The `RnExpr` for the AX/BY cevian-pair denominator `D := (1-q) + p*q` --
/// see the module note. A function of `p, q` alone, independent of the
/// triangle.
fn rn_cevian_d(pp: RnExpr, qq: RnExpr) -> RnExpr {
    RnExpr::add(rn_one_minus(qq.clone()), RnExpr::mul(pp, qq))
}

/// The `RnExpr` for the `AX` cevian parameter `t := (1-q)*z`.
fn rn_cevian_t(qq: RnExpr, z: RnExpr) -> RnExpr {
    RnExpr::mul(rn_one_minus(qq), z)
}

/// The `RnExpr` for the `BY` cevian parameter `u := p*z`.
fn rn_cevian_u(pp: RnExpr, z: RnExpr) -> RnExpr {
    RnExpr::mul(pp, z)
}

/// The `RnExpr` for the `CZ` cevian parameter `v := (1 - p - q + 2*p*q)*z`.
fn rn_cevian_v(pp: RnExpr, qq: RnExpr, z: RnExpr) -> RnExpr {
    let pq = RnExpr::mul(pp.clone(), qq.clone());
    let coeff = RnExpr::add(
        RnExpr::add(rn_one_minus(pp), RnExpr::neg(qq)),
        RnExpr::add(pq.clone(), pq),
    );
    RnExpr::mul(coeff, z)
}

/// The `RnExpr` for the Ceva ratio product `p*q*r`.
fn rn_ceva_lhs(pp: RnExpr, qq: RnExpr, rr: RnExpr) -> RnExpr {
    RnExpr::mul(pp, RnExpr::mul(qq, rr))
}

/// The `RnExpr` for `(1-p)*(1-q)*(1-r)`.
fn rn_ceva_rhs(pp: RnExpr, qq: RnExpr, rr: RnExpr) -> RnExpr {
    RnExpr::mul(
        rn_one_minus(pp),
        RnExpr::mul(rn_one_minus(qq), rn_one_minus(rr)),
    )
}

/// The `RnExpr` for the Ceva ratio defect `p*q*r - (1-p)*(1-q)*(1-r)`, built
/// from [`rn_ceva_lhs`]/[`rn_ceva_rhs`] (never re-typed) so that
/// [`sub_eq_zero_of_equiv`] applied to a `hCeva : Equiv (rn_ceva_lhs …)
/// (rn_ceva_rhs …)` hypothesis produces a proof about exactly the same term
/// this renders to.
fn rn_ceva_defect(pp: RnExpr, qq: RnExpr, rr: RnExpr) -> RnExpr {
    RnExpr::add(
        rn_ceva_lhs(pp.clone(), qq.clone(), rr.clone()),
        RnExpr::neg(rn_ceva_rhs(pp, qq, rr)),
    )
}

/// `D := (1-q) + p*q`, as a concrete term -- built via [`rn_cevian_d`]/
/// [`rn_render`] (not a hand-typed `cadd`/`cmul` chain) so every other call
/// site that also goes through `rn_cevian_d` on the same `pp, qq` lands on
/// this exact `ExprId` (hash-consing; see the module note).
fn cevian_big_d(d: &mut IntDev<'_>, p: CPointPrelude, pp: ExprId, qq: ExprId) -> ExprId {
    let creal = p.creal;
    let d_r = rn_cevian_d(RnExpr::Atom(pp), RnExpr::Atom(qq));
    rn_render(d, creal, &d_r)
}

/// `z := D * CReal.inv (mul D D) k h` -- "`1/D`" without ever inspecting
/// `D`'s sign, mirroring [`CPointPrelude::non_collinear`]'s own squaring
/// trick (see the module note).
fn cevian_dinv(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    big_d: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let dd = cmul(d, p, big_d, big_d);
    let inv_dd = d.const_app(creal.inv, &[dd, k, h]);
    cmul(d, p, big_d, inv_dd)
}

/// `Equiv (mul D z) one`, `z` as built by [`cevian_dinv`] at the same
/// `big_d, k, h`: `D*z ~ (D*D)*inv_dd` (`mul_assoc`, reversed) `~ one`
/// (`mul_inv_cancel`).
fn cevian_dinv_cancel(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    big_d: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let dd = cmul(d, p, big_d, big_d);
    let inv_dd = d.const_app(creal.inv, &[dd, k, h]);
    let d_inv_dd = cmul(d, p, big_d, inv_dd);
    let d_z = cmul(d, p, big_d, d_inv_dd);
    let dd_invdd = cmul(d, p, dd, inv_dd);
    let assoc = d.lemma(creal.mul_assoc, &[big_d, big_d, inv_dd]); // Equiv(dd_invdd, d_z)
    let assoc_symm = symm(d, p, dd_invdd, d_z, assoc); // Equiv(d_z, dd_invdd)
    let cancel_dd = d.lemma(creal.mul_inv_cancel, &[dd, k, h]); // Equiv(dd_invdd, one)
    let one = d.kernel().const_(creal.one, vec![]);
    chain(d, p, d_z, &[(dd_invdd, assoc_symm), (one, cancel_dd)])
}

/// `(correction, proof : Equiv correction CReal.zero)`, `correction := mul
/// (add (mul D z) (neg one)) diff`, given `dz_cancel : Equiv (mul D z) one`.
/// The single-term correction [`cevian_pair_ax_by_scalar_proof`] needs, and
/// the first half of what [`cevian_correction2_zero`] needs.
fn cevian_correction_zero(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    big_d: ExprId,
    z: ExprId,
    diff: ExprId,
    dz_cancel: ExprId,
) -> (ExprId, ExprId) {
    let creal = p.creal;
    let one = d.kernel().const_(creal.one, vec![]);
    let d_z = cmul(d, p, big_d, z);
    let neg_one = cneg(d, p, one);
    let dz_minus_one = cadd(d, p, d_z, neg_one);
    let dz_zero = sub_eq_zero_of_equiv(d, p, d_z, one, dz_cancel); // Equiv dz_minus_one zero
    let zero = czero(d, p);
    let refl_diff = refl(d, p, diff);
    let correction = cmul(d, p, dz_minus_one, diff);
    let zero_diff = cmul(d, p, zero, diff);
    let congr = d.lemma(
        creal.mul_congr,
        &[dz_minus_one, zero, diff, diff, dz_zero, refl_diff],
    );
    let zm = zero_mul_proof(d, p, diff);
    let proof = chain(d, p, correction, &[(zero_diff, congr), (zero, zm)]);
    (correction, proof)
}

/// `(correction, proof : Equiv correction CReal.zero)`, `correction := add
/// (mul (add (mul D z) (neg one)) diff1) (mul (mul z diff2) defect)`, given
/// `dz_cancel : Equiv (mul D z) one` and `defect_zero : Equiv defect
/// CReal.zero`. The BY/CZ cevian-pair correction term (see the module
/// note): unlike [`cevian_correction_zero`] it needs BOTH the denominator
/// witness and the Ceva ratio condition to vanish.
fn cevian_correction2_zero(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    big_d: ExprId,
    z: ExprId,
    diff1: ExprId,
    diff2: ExprId,
    dz_cancel: ExprId,
    defect: ExprId,
    defect_zero: ExprId,
) -> (ExprId, ExprId) {
    let creal = p.creal;
    let zero = czero(d, p);

    let (term1, term1_zero) = cevian_correction_zero(d, p, big_d, z, diff1, dz_cancel);

    let z_diff2 = cmul(d, p, z, diff2);
    let term2 = cmul(d, p, z_diff2, defect);
    let refl_zd = refl(d, p, z_diff2);
    let congr2 = d.lemma(
        creal.mul_congr,
        &[z_diff2, z_diff2, defect, zero, refl_zd, defect_zero],
    ); // Equiv term2 (mul z_diff2 zero)
    let mz = d.lemma(creal.mul_zero, &[z_diff2]); // Equiv (mul z_diff2 zero) zero
    let zero_zd = cmul(d, p, z_diff2, zero);
    let term2_zero = chain(d, p, term2, &[(zero_zd, congr2), (zero, mz)]);

    let correction2 = cadd(d, p, term1, term2);
    let congr_sum = d.lemma(
        creal.add_congr,
        &[term1, zero, term2, zero, term1_zero, term2_zero],
    ); // Equiv correction2 (add zero zero)
    let zero_zero = cadd(d, p, zero, zero);
    let az = d.lemma(creal.add_zero, &[zero]); // Equiv (add zero zero) zero
    let proof = chain(d, p, correction2, &[(zero_zero, congr_sum), (zero, az)]);
    (correction2, proof)
}

/// One coordinate of the `AX`/`BY` cevian pair. `a, b, c` stand for the
/// shared coordinate (`x` or `y`) of `A, B, C`; `pp, qq` are the cevian
/// ratios `p, q`; `z, big_d` are [`cevian_dinv`]/[`cevian_big_d`]'s outputs
/// at these same `pp, qq` (and some `k, h`, not needed again here);
/// `dz_cancel` is [`cevian_dinv_cancel`]'s proof at those same values --
/// the caller is responsible for that consistency, not re-derived here (see
/// the module note on why the shapes must match by construction).
///
/// Proves `Equiv (lerp a (lerp b c pp) t) (lerp b (lerp c a qq) u)`,
/// `t := (1-qq)*z`, `u := pp*z`, via the pure ring identity
/// `lerp a (lerp b c pp) t - lerp b (lerp c a qq) u ~ (D*z - 1)*(b - a)`
/// (checked exactly with `sympy`, see the module note) plus
/// [`cevian_correction_zero`].
fn cevian_pair_ax_by_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    pp: ExprId,
    qq: ExprId,
    z: ExprId,
    big_d: ExprId,
    dz_cancel: ExprId,
) -> ExprId {
    let creal = p.creal;

    let a_r = RnExpr::Atom(a);
    let b_r = RnExpr::Atom(b);
    let c_r = RnExpr::Atom(c);
    let pp_r = RnExpr::Atom(pp);
    let qq_r = RnExpr::Atom(qq);
    let z_r = RnExpr::Atom(z);

    let t_r = rn_cevian_t(qq_r.clone(), z_r.clone());
    let u_r = rn_cevian_u(pp_r.clone(), z_r.clone());

    let x_r = rn_lerp(b_r.clone(), c_r.clone(), pp_r);
    let y_r = rn_lerp(c_r.clone(), a_r.clone(), qq_r.clone());

    let lhs_r = rn_lerp(a_r.clone(), x_r, t_r);
    let rhs_main_r = rn_lerp(b_r.clone(), y_r, u_r);

    let d_r = rn_cevian_d(RnExpr::Atom(pp), qq_r);
    let dz_minus_one_r = RnExpr::add(RnExpr::mul(d_r, z_r), RnExpr::neg(RnExpr::One));
    let ba_r = rn_diff(b_r.clone(), a_r.clone());
    let correction_r = RnExpr::mul(dz_minus_one_r, ba_r);

    let rhs_full_r = RnExpr::add(rhs_main_r.clone(), correction_r);

    let ring_pf = rn_ring_proof(d, creal, &lhs_r, &rhs_full_r);

    let lhs_actual = rn_render(d, creal, &lhs_r);
    let rhs_main_actual = rn_render(d, creal, &rhs_main_r);
    let rhs_full_actual = rn_render(d, creal, &rhs_full_r);

    let neg_a = cneg(d, p, a);
    let ba = cadd(d, p, b, neg_a);
    let (correction_actual, correction_zero_pf) =
        cevian_correction_zero(d, p, big_d, z, ba, dz_cancel);
    let _ = correction_actual; // consistency guaranteed by construction, see module note

    let zero = czero(d, p);
    let refl_rhs_main = refl(d, p, rhs_main_actual);
    let congr_rhs = d.lemma(
        creal.add_congr,
        &[
            rhs_main_actual,
            rhs_main_actual,
            correction_actual,
            zero,
            refl_rhs_main,
            correction_zero_pf,
        ],
    );
    let rhs_plus_zero = cadd(d, p, rhs_main_actual, zero);
    let az = d.lemma(creal.add_zero, &[rhs_main_actual]);

    chain(
        d,
        p,
        lhs_actual,
        &[
            (rhs_full_actual, ring_pf),
            (rhs_plus_zero, congr_rhs),
            (rhs_main_actual, az),
        ],
    )
}

/// **The `AX`/`BY` cevian-pair meeting point, exhibited explicitly.** See
/// [`CPointPrelude::cevian_pair_meet`].
fn declare_cevian_pair_meet(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let k_fv = d.fresh_fvar();
    let pk = d.kernel().fvar(k_fv);

    let big_d = cevian_big_d(d, p, pp, qq);
    let dd = cmul(d, p, big_d, big_d);
    let hd_ty = d.const_app(creal.pos_bound, &[dd, pk]);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let z = cevian_dinv(d, p, big_d, pk, hd);
    let dz_cancel = cevian_dinv_cancel(d, p, big_d, pk, hd);

    let t_expr = rn_render(d, creal, &rn_cevian_t(RnExpr::Atom(qq), RnExpr::Atom(z)));
    let u_expr = rn_render(d, creal, &rn_cevian_u(RnExpr::Atom(pp), RnExpr::Atom(z)));

    let big_x = d.const_app(p.point_lerp, &[pb, pc, pp]);
    let big_y = d.const_app(p.point_lerp, &[pc, pa, qq]);
    let lhs_point = d.const_app(p.point_lerp, &[pa, big_x, t_expr]);
    let rhs_point = d.const_app(p.point_lerp, &[pb, big_y, u_expr]);

    let ax = d.const_app(p.x, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let ay = d.const_app(p.y, &[pa]);
    let by = d.const_app(p.y, &[pb]);
    let cy = d.const_app(p.y, &[pc]);

    let proof_x = cevian_pair_ax_by_scalar_proof(d, p, ax, bx, cx, pp, qq, z, big_d, dz_cancel);
    let proof_y = cevian_pair_ax_by_scalar_proof(d, p, ay, by, cy, pp, qq, z, big_d, dz_cancel);

    let lhs_x = d.const_app(p.x, &[lhs_point]);
    let rhs_x = d.const_app(p.x, &[rhs_point]);
    let lhs_y = d.const_app(p.y, &[lhs_point]);
    let rhs_y = d.const_app(p.y, &[rhs_point]);
    let claim_x = equiv(d, p, lhs_x, rhs_x);
    let claim_y = equiv(d, p, lhs_y, rhs_y);
    let body = and_intro(d, p, claim_x, claim_y, proof_x, proof_y);
    let concl = d.const_app(p.point_equiv, &[lhs_point, rhs_point]);

    let ty_body = {
        let inner = d.pi_fv(hd_fv, hd_ty, concl);
        let w1 = d.pi_fv(k_fv, nat, inner);
        let w2 = d.pi_fv(qq_fv, carrier, w1);
        d.pi_fv(pp_fv, carrier, w2)
    };
    let ty = {
        let w1 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w1);
        d.pi_fv(a_fv, point, w2)
    };
    let value_body = {
        let inner = d.lam_fv(hd_fv, hd_ty, body);
        let w1 = d.lam_fv(k_fv, nat, inner);
        let w2 = d.lam_fv(qq_fv, carrier, w1);
        d.lam_fv(pp_fv, carrier, w2)
    };
    let value = {
        let w1 = d.lam_fv(c_fv, point, value_body);
        let w2 = d.lam_fv(b_fv, point, w1);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cevian_pair_meet,
        uparams: vec![],
        ty,
        value,
    })
}

/// One coordinate of the `BY`/`CZ` cevian pair, discharging the Ceva ratio
/// condition. `a, b, c` are the shared coordinate of `A, B, C`; `pp, qq, rr`
/// the three ratios; `z, big_d, dz_cancel` as in
/// [`cevian_pair_ax_by_scalar_proof`] (same `pp, qq` and some `k, h`);
/// `defect` is [`rn_ceva_defect`]'s rendered term at `pp, qq, rr` and
/// `defect_zero` a proof that it is `Equiv`-zero (from the Ceva ratio
/// hypothesis via [`sub_eq_zero_of_equiv`]) -- the caller builds both, so
/// the same `ExprId` is used here as in the Ceva hypothesis's own type (see
/// the module note on why that consistency matters and how it is
/// guaranteed).
///
/// Proves `Equiv (lerp b (lerp c a qq) u) (lerp c (lerp a b rr) v)`,
/// `u := pp*z`, `v := (1 - pp - qq + 2*pp*qq)*z`, via the pure ring identity
/// `lerp b (lerp c a qq) u - lerp c (lerp a b rr) v ~
///    (D*z - 1)*(c - b) + (z*(a - b)) * defect`
/// (checked exactly with `sympy`, see the module note) plus
/// [`cevian_correction2_zero`].
fn cevian_pair_by_cz_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    pp: ExprId,
    qq: ExprId,
    rr: ExprId,
    z: ExprId,
    big_d: ExprId,
    dz_cancel: ExprId,
    defect: ExprId,
    defect_zero: ExprId,
) -> ExprId {
    let creal = p.creal;

    let a_r = RnExpr::Atom(a);
    let b_r = RnExpr::Atom(b);
    let c_r = RnExpr::Atom(c);
    let pp_r = RnExpr::Atom(pp);
    let qq_r = RnExpr::Atom(qq);
    let rr_r = RnExpr::Atom(rr);
    let z_r = RnExpr::Atom(z);

    let u_r = rn_cevian_u(pp_r.clone(), z_r.clone());
    let v_r = rn_cevian_v(pp_r.clone(), qq_r.clone(), z_r.clone());

    let y_r = rn_lerp(c_r.clone(), a_r.clone(), qq_r.clone());
    let z_pt_r = rn_lerp(a_r.clone(), b_r.clone(), rr_r.clone());

    let lhs_r = rn_lerp(b_r.clone(), y_r, u_r);
    let rhs_main_r = rn_lerp(c_r.clone(), z_pt_r, v_r);

    let d_r = rn_cevian_d(pp_r.clone(), qq_r.clone());
    let dz_minus_one_r = RnExpr::add(RnExpr::mul(d_r, z_r.clone()), RnExpr::neg(RnExpr::One));
    let cb_r = rn_diff(c_r.clone(), b_r.clone());
    let term1_r = RnExpr::mul(dz_minus_one_r, cb_r);

    let ab_r = rn_diff(a_r.clone(), b_r.clone());
    let z_ab_r = RnExpr::mul(z_r, ab_r);
    let defect_r = rn_ceva_defect(pp_r, qq_r, rr_r);
    let term2_r = RnExpr::mul(z_ab_r, defect_r);

    let correction_r = RnExpr::add(term1_r, term2_r);
    let rhs_full_r = RnExpr::add(rhs_main_r.clone(), correction_r);

    let ring_pf = rn_ring_proof(d, creal, &lhs_r, &rhs_full_r);

    let lhs_actual = rn_render(d, creal, &lhs_r);
    let rhs_main_actual = rn_render(d, creal, &rhs_main_r);
    let rhs_full_actual = rn_render(d, creal, &rhs_full_r);

    let neg_b1 = cneg(d, p, b);
    let cb = cadd(d, p, c, neg_b1);
    let neg_b2 = cneg(d, p, b);
    let ab = cadd(d, p, a, neg_b2);
    let (correction_actual, correction_zero_pf) =
        cevian_correction2_zero(d, p, big_d, z, cb, ab, dz_cancel, defect, defect_zero);
    let _ = correction_actual; // consistency guaranteed by construction, see module note

    let zero = czero(d, p);
    let refl_rhs_main = refl(d, p, rhs_main_actual);
    let congr_rhs = d.lemma(
        creal.add_congr,
        &[
            rhs_main_actual,
            rhs_main_actual,
            correction_actual,
            zero,
            refl_rhs_main,
            correction_zero_pf,
        ],
    );
    let rhs_plus_zero = cadd(d, p, rhs_main_actual, zero);
    let az = d.lemma(creal.add_zero, &[rhs_main_actual]);

    chain(
        d,
        p,
        lhs_actual,
        &[
            (rhs_full_actual, ring_pf),
            (rhs_plus_zero, congr_rhs),
            (rhs_main_actual, az),
        ],
    )
}

/// **Ceva's theorem, exhibiting direction.** See
/// [`CPointPrelude::ceva_concurrent_of_ratio_product`].
fn declare_ceva_concurrent_of_ratio_product(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let rr_fv = d.fresh_fvar();
    let rr = d.kernel().fvar(rr_fv);
    let k_fv = d.fresh_fvar();
    let pk = d.kernel().fvar(k_fv);

    let big_d = cevian_big_d(d, p, pp, qq);
    let dd = cmul(d, p, big_d, big_d);
    let hd_ty = d.const_app(creal.pos_bound, &[dd, pk]);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let ceva_lhs_expr = rn_render(
        d,
        creal,
        &rn_ceva_lhs(RnExpr::Atom(pp), RnExpr::Atom(qq), RnExpr::Atom(rr)),
    );
    let ceva_rhs_expr = rn_render(
        d,
        creal,
        &rn_ceva_rhs(RnExpr::Atom(pp), RnExpr::Atom(qq), RnExpr::Atom(rr)),
    );
    let hceva_ty = equiv(d, p, ceva_lhs_expr, ceva_rhs_expr);
    let hceva_fv = d.fresh_fvar();
    let hceva = d.kernel().fvar(hceva_fv);

    let z = cevian_dinv(d, p, big_d, pk, hd);
    let dz_cancel = cevian_dinv_cancel(d, p, big_d, pk, hd);

    let t_expr = rn_render(d, creal, &rn_cevian_t(RnExpr::Atom(qq), RnExpr::Atom(z)));
    let u_expr = rn_render(d, creal, &rn_cevian_u(RnExpr::Atom(pp), RnExpr::Atom(z)));
    let v_expr = rn_render(
        d,
        creal,
        &rn_cevian_v(RnExpr::Atom(pp), RnExpr::Atom(qq), RnExpr::Atom(z)),
    );

    let big_x = d.const_app(p.point_lerp, &[pb, pc, pp]);
    let big_y = d.const_app(p.point_lerp, &[pc, pa, qq]);
    let big_z = d.const_app(p.point_lerp, &[pa, pb, rr]);
    let ax_point = d.const_app(p.point_lerp, &[pa, big_x, t_expr]);
    let by_point = d.const_app(p.point_lerp, &[pb, big_y, u_expr]);
    let cz_point = d.const_app(p.point_lerp, &[pc, big_z, v_expr]);

    let defect = rn_render(
        d,
        creal,
        &rn_ceva_defect(RnExpr::Atom(pp), RnExpr::Atom(qq), RnExpr::Atom(rr)),
    );
    let defect_zero = sub_eq_zero_of_equiv(d, p, ceva_lhs_expr, ceva_rhs_expr, hceva);

    // -- first conjunct: AX meets BY --------------------------------------
    let ax = d.const_app(p.x, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let ay = d.const_app(p.y, &[pa]);
    let by_ = d.const_app(p.y, &[pb]);
    let cy = d.const_app(p.y, &[pc]);

    let pf1_x = cevian_pair_ax_by_scalar_proof(d, p, ax, bx, cx, pp, qq, z, big_d, dz_cancel);
    let pf1_y = cevian_pair_ax_by_scalar_proof(d, p, ay, by_, cy, pp, qq, z, big_d, dz_cancel);

    let ax_x = d.const_app(p.x, &[ax_point]);
    let by_x = d.const_app(p.x, &[by_point]);
    let ax_y = d.const_app(p.y, &[ax_point]);
    let by_y = d.const_app(p.y, &[by_point]);
    let claim1_x = equiv(d, p, ax_x, by_x);
    let claim1_y = equiv(d, p, ax_y, by_y);
    let body1 = and_intro(d, p, claim1_x, claim1_y, pf1_x, pf1_y);
    let concl1 = d.const_app(p.point_equiv, &[ax_point, by_point]);

    // -- second conjunct: BY meets CZ, via the Ceva ratio condition -------
    let pf2_x = cevian_pair_by_cz_scalar_proof(
        d,
        p,
        ax,
        bx,
        cx,
        pp,
        qq,
        rr,
        z,
        big_d,
        dz_cancel,
        defect,
        defect_zero,
    );
    let pf2_y = cevian_pair_by_cz_scalar_proof(
        d,
        p,
        ay,
        by_,
        cy,
        pp,
        qq,
        rr,
        z,
        big_d,
        dz_cancel,
        defect,
        defect_zero,
    );

    let by_x2 = d.const_app(p.x, &[by_point]);
    let cz_x = d.const_app(p.x, &[cz_point]);
    let by_y2 = d.const_app(p.y, &[by_point]);
    let cz_y = d.const_app(p.y, &[cz_point]);
    let claim2_x = equiv(d, p, by_x2, cz_x);
    let claim2_y = equiv(d, p, by_y2, cz_y);
    let body2 = and_intro(d, p, claim2_x, claim2_y, pf2_x, pf2_y);
    let concl2 = d.const_app(p.point_equiv, &[by_point, cz_point]);

    let body = and_intro(d, p, concl1, concl2, body1, body2);
    let concl = {
        let and_ = p.creal.rat.int.logic.and;
        d.const_app(and_, &[concl1, concl2])
    };

    let ty_body = {
        let inner = d.pi_fv(hceva_fv, hceva_ty, concl);
        let w1 = d.pi_fv(hd_fv, hd_ty, inner);
        let w2 = d.pi_fv(k_fv, nat, w1);
        let w3 = d.pi_fv(rr_fv, carrier, w2);
        let w4 = d.pi_fv(qq_fv, carrier, w3);
        d.pi_fv(pp_fv, carrier, w4)
    };
    let ty = {
        let w1 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w1);
        d.pi_fv(a_fv, point, w2)
    };
    let value_body = {
        let inner = d.lam_fv(hceva_fv, hceva_ty, body);
        let w1 = d.lam_fv(hd_fv, hd_ty, inner);
        let w2 = d.lam_fv(k_fv, nat, w1);
        let w3 = d.lam_fv(rr_fv, carrier, w2);
        let w4 = d.lam_fv(qq_fv, carrier, w3);
        d.lam_fv(pp_fv, carrier, w4)
    };
    let value = {
        let w1 = d.lam_fv(c_fv, point, value_body);
        let w2 = d.lam_fv(b_fv, point, w1);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ceva_concurrent_of_ratio_product,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// Menelaus' theorem and the converse of Ceva.
//
// Menelaus: same `X, Y, Z` as Ceva (`X := lerp B C p`, `Y := lerp C A q`,
// `Z := lerp A B r`), but the claim is that `X, Y, Z` are COLLINEAR (a
// transversal line cutting the three sides, possibly extended) rather than
// that the three cevians `AX, BY, CZ` are concurrent. The division-free
// ratio-product condition picks up a sign flip relative to Ceva: checked
// exactly with `sympy` (`ax,ay,bx,by,cx,cy,p,q,r` symbolic, `cross X Y Z`
// expanded and polynomial-divided by `cross A B C`), the quotient is EXACTLY
// `p*q*r + (1-p)*(1-q)*(1-r)` with zero remainder:
//
//     cross X Y Z  ~  (p*q*r + (1-p)*(1-q)*(1-r)) * cross A B C
//
// an unconditional polynomial identity (`A = B = C` included, matching the
// Ceva lane's finding that `D` needs no `NonCollinear` hypothesis). So
// Menelaus' division-free form is the SUM `p*q*r + (1-p)*(1-q)*(1-r) ~ 0`,
// i.e. `p*q*r ~ -(1-p)*(1-q)*(1-r)` -- the sign-flipped analogue of Ceva's
// `p*q*r ~ (1-p)*(1-q)*(1-r)`, exactly as sketched. Ceva's own defect
// `p*q*r - (1-p)*(1-q)*(1-r)` does NOT appear here at all (residual nonzero
// for both signs of that quotient), so the two theorems are genuinely
// different polynomial identities, not the same one restated.
//
// The Ceva converse is a different kind of statement: given that the
// canonical `BY`/`CZ` meeting point (the same `u, v` the exhibiting
// direction uses) actually coincides, recover the ratio product. Route in
// the section below the Menelaus declaration.

/// The `RnExpr` for `cross` applied to six raw coordinate values, mirroring
/// [`cross_raw`]'s construction call-for-call (`u := qx-px, v := ry-qy, w :=
/// qy-py, z := rx-qx`, value `u*v - w*z`) so `rn_render` of this lands on
/// exactly the `ExprId` [`cross_raw`] builds from the same coordinate atoms
/// (interning; see the module note on why the `rn_*` trees must mirror the
/// actual-term builders exactly, not just be ring-equal to them).
fn rn_cross(px: RnExpr, py: RnExpr, qx: RnExpr, qy: RnExpr, rx: RnExpr, ry: RnExpr) -> RnExpr {
    let u = rn_diff(qx.clone(), px);
    let v = rn_diff(ry, qy.clone());
    let w = rn_diff(qy, py);
    let z = rn_diff(rx, qx);
    let uv = RnExpr::mul(u, v);
    let wz = RnExpr::mul(w, z);
    RnExpr::add(uv, RnExpr::neg(wz))
}

/// The `RnExpr` mirror of [`CPointPrelude::dist_sq`]'s own full delta/iota
/// unfolding: `distSq P Q` reduces -- through `dist_sq`'s definition, then
/// `dot`'s, then `sub`'s, then the `x`/`y` projections of `sub`'s `mk`
/// constructor -- to exactly `(px-qx)*(px-qx) + (py-qy)*(py-qy)`. Mirrors
/// [`rn_cross`]'s role for [`CPointPrelude::cross`]. Already-proven
/// precedent that the kernel accepts exactly this depth of unfolding when
/// checking a `dist_sq`-headed declared type against a raw-coordinate
/// value: `declare_dist_sq_self_zero`'s own `sum` local (`== dot(sub pa pa,
/// sub pa pa) == distSq pa pa`) is the identical shape at `P = Q`.
fn rn_dist_sq(px: RnExpr, py: RnExpr, qx: RnExpr, qy: RnExpr) -> RnExpr {
    let dx = rn_diff(px, qx);
    let dy = rn_diff(py, qy);
    RnExpr::add(RnExpr::mul(dx.clone(), dx), RnExpr::mul(dy.clone(), dy))
}

/// The `RnExpr` for the Menelaus ratio defect `p*q*r + (1-p)*(1-q)*(1-r)`
/// (the SUM, not [`rn_ceva_defect`]'s difference -- see the module note on
/// the sign flip). Built from [`rn_ceva_lhs`]/[`rn_ceva_rhs`] so a term
/// mirroring this shape lands on the same `ExprId`s those produce.
fn rn_menelaus_defect(pp: RnExpr, qq: RnExpr, rr: RnExpr) -> RnExpr {
    RnExpr::add(
        rn_ceva_lhs(pp.clone(), qq.clone(), rr.clone()),
        rn_ceva_rhs(pp, qq, rr),
    )
}

/// **Menelaus' theorem, collinear-of-ratio-product direction.** See
/// [`CPointPrelude::menelaus_collinear_of_ratio_product`].
fn declare_menelaus_collinear_of_ratio_product(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let rr_fv = d.fresh_fvar();
    let rr = d.kernel().fvar(rr_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);

    let ax_r = RnExpr::Atom(ax);
    let ay_r = RnExpr::Atom(ay);
    let bx_r = RnExpr::Atom(bx);
    let by_r = RnExpr::Atom(by);
    let cx_r = RnExpr::Atom(cx);
    let cy_r = RnExpr::Atom(cy);
    let pp_r = RnExpr::Atom(pp);
    let qq_r = RnExpr::Atom(qq);
    let rr_r = RnExpr::Atom(rr);

    // -- the ratio-product hypothesis: `p*q*r ~ neg ((1-p)*(1-q)*(1-r))` ---
    let ceva_lhs_expr = rn_render(
        d,
        creal,
        &rn_ceva_lhs(pp_r.clone(), qq_r.clone(), rr_r.clone()),
    );
    let ceva_rhs_expr = rn_render(
        d,
        creal,
        &rn_ceva_rhs(pp_r.clone(), qq_r.clone(), rr_r.clone()),
    );
    let neg_ceva_rhs_expr = cneg(d, p, ceva_rhs_expr);
    let hmen_ty = equiv(d, p, ceva_lhs_expr, neg_ceva_rhs_expr);
    let hmen_fv = d.fresh_fvar();
    let hmen = d.kernel().fvar(hmen_fv);

    // `defect_actual := add ceva_lhs_expr (neg neg_ceva_rhs_expr)`, `~ zero`
    // from `hmen` via `sub_eq_zero_of_equiv` -- ring-equal to (but not
    // syntactically) `rn_menelaus_defect`'s render, since it carries the
    // extra double negation `sub_eq_zero_of_equiv` always produces.
    let raw_defect_zero = sub_eq_zero_of_equiv(d, p, ceva_lhs_expr, neg_ceva_rhs_expr, hmen);
    let raw_defect_r = RnExpr::add(
        rn_ceva_lhs(pp_r.clone(), qq_r.clone(), rr_r.clone()),
        RnExpr::neg(RnExpr::neg(rn_ceva_rhs(
            pp_r.clone(),
            qq_r.clone(),
            rr_r.clone(),
        ))),
    );
    let clean_defect_r = rn_menelaus_defect(pp_r.clone(), qq_r.clone(), rr_r.clone());

    // -- the point coordinates of X, Y, Z -----------------------------------
    let xx_r = rn_lerp(bx_r.clone(), cx_r.clone(), pp_r.clone());
    let xy_r = rn_lerp(by_r.clone(), cy_r.clone(), pp_r.clone());
    let yx_r = rn_lerp(cx_r.clone(), ax_r.clone(), qq_r.clone());
    let yy_r = rn_lerp(cy_r.clone(), ay_r.clone(), qq_r.clone());
    let zx_r = rn_lerp(ax_r.clone(), bx_r.clone(), rr_r.clone());
    let zy_r = rn_lerp(ay_r.clone(), by_r.clone(), rr_r.clone());

    let cross_xyz_r = rn_cross(xx_r, xy_r, yx_r, yy_r, zx_r, zy_r);
    let cross_abc_r = rn_cross(ax_r, ay_r, bx_r, by_r, cx_r, cy_r);

    // -- the pure ring identity: `cross X Y Z ~ raw_defect * cross A B C` --
    let target_r = RnExpr::mul(raw_defect_r, cross_abc_r.clone());
    let ring_pf = rn_ring_proof(d, creal, &cross_xyz_r, &target_r);

    let cross_xyz_actual = rn_render(d, creal, &cross_xyz_r);
    let cross_abc_actual = rn_render(d, creal, &cross_abc_r);
    // Built directly from `ceva_lhs_expr`/`neg_ceva_rhs_expr` (not re-derived
    // via `rn_render`) so it is *by construction* the same `ExprId`
    // `sub_eq_zero_of_equiv` used internally (`cadd u (cneg v)`), matching
    // `raw_defect_zero`'s type exactly.
    let neg_neg_ceva_rhs_expr = cneg(d, p, neg_ceva_rhs_expr);
    let raw_defect_actual = cadd(d, p, ceva_lhs_expr, neg_neg_ceva_rhs_expr);
    let _ = clean_defect_r; // documents the "clean" shape; not separately rendered

    let target_actual = cmul(d, p, raw_defect_actual, cross_abc_actual);
    let zero = czero(d, p);
    let refl_cross_abc = refl(d, p, cross_abc_actual);
    let congr = d.lemma(
        creal.mul_congr,
        &[
            raw_defect_actual,
            zero,
            cross_abc_actual,
            cross_abc_actual,
            raw_defect_zero,
            refl_cross_abc,
        ],
    );
    let zero_cross_abc = cmul(d, p, zero, cross_abc_actual);
    let zm = zero_mul_proof(d, p, cross_abc_actual);

    let proof = chain(
        d,
        p,
        cross_xyz_actual,
        &[
            (target_actual, ring_pf),
            (zero_cross_abc, congr),
            (zero, zm),
        ],
    );

    // -- the theorem's stated conclusion, at the Point level ---------------
    let big_x = d.const_app(p.point_lerp, &[pb, pc, pp]);
    let big_y = d.const_app(p.point_lerp, &[pc, pa, qq]);
    let big_z = d.const_app(p.point_lerp, &[pa, pb, rr]);
    let cross_xyz_stated = d.const_app(p.cross, &[big_x, big_y, big_z]);
    let concl = equiv(d, p, cross_xyz_stated, zero);

    let ty_body = {
        let inner = d.pi_fv(hmen_fv, hmen_ty, concl);
        let w1 = d.pi_fv(rr_fv, carrier, inner);
        let w2 = d.pi_fv(qq_fv, carrier, w1);
        d.pi_fv(pp_fv, carrier, w2)
    };
    let ty = {
        let w1 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w1);
        d.pi_fv(a_fv, point, w2)
    };
    let value_body = {
        let inner = d.lam_fv(hmen_fv, hmen_ty, proof);
        let w1 = d.lam_fv(rr_fv, carrier, inner);
        let w2 = d.lam_fv(qq_fv, carrier, w1);
        d.lam_fv(pp_fv, carrier, w2)
    };
    let value = {
        let w1 = d.lam_fv(c_fv, point, value_body);
        let w2 = d.lam_fv(b_fv, point, w1);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.menelaus_collinear_of_ratio_product,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// The converse of Ceva: concurrency implies the ratio product.
//
// The exhibiting direction (`ceva_concurrent_of_ratio_product`) never proves
// the `BY`/`CZ` meeting point is UNIQUE, so the converse cannot honestly
// hypothesize "some point on all three cevians" without first building that
// uniqueness argument (a separate, harder result). Instead this hypothesizes
// concurrency at the SAME canonical parametrisation the exhibiting direction
// uses (`u := p*z, v := (1-p-q+2pq)*z`, `z` from `D ≠ 0`): `CPoint.Equiv
// (lerp B Y u) (lerp C Z v)`. Given `D ≠ 0`, `AX ~ BY` is already forced
// (`cevian_pair_meet`, no Ceva hypothesis needed), so this hypothesis is
// exactly "the point where AX, BY already necessarily meet also lies on
// CZ" -- concurrency, for this configuration.
//
// `cevian_pair_by_cz_scalar_proof`'s ring identity (`lerp b Y u - lerp c Z v
// ~ (D*z-1)*(c-b) + (z*(a-b))*defect`) runs in REVERSE: the hypothesis
// forces the left side to `~ 0`; the first summand is `~ 0` unconditionally
// (from `D*z ~ 1`, [`cevian_correction_zero`]); so the second summand is `~
// 0`. Multiplying through by `D` cancels the shared `z` factor via `D*z ~
// 1` -- no need for `z` itself to be invertible -- leaving `(a-b)*defect ~
// 0` at BOTH coordinates (`a,b` being `A,B`'s `x` and `y` respectively).
// Squaring and summing those two turns them into `distSq A B * defect² ~
// 0`; `distSq A B` invertible (the extra non-degeneracy, `A ≠ B`) cancels it
// to `defect² ~ 0`, and `eq_zero_of_mul_self_zero` finishes at `defect ~ 0`,
// i.e. the Ceva ratio equation.

/// The pure ring identity behind [`cevian_pair_by_cz_scalar_proof`], split
/// into its pieces with NO hypothesis consumed (unlike that function, which
/// needs `dz_cancel`/`defect_zero` to simplify further) -- exactly what the
/// converse needs to run the identity in reverse. Returns `(lhs_actual,
/// rhs_main_actual, term1_actual, term2_actual, rhs_full_actual, ab_actual)`
/// where `ring_pf : Equiv lhs_actual rhs_full_actual` and `rhs_full_actual`
/// is BY CONSTRUCTION `add rhs_main_actual (add term1_actual term2_actual)`.
#[allow(clippy::too_many_arguments)]
fn cevian_by_cz_ring_split(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    pp: ExprId,
    qq: ExprId,
    rr: ExprId,
    z: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) {
    let creal = p.creal;

    let a_r = RnExpr::Atom(a);
    let b_r = RnExpr::Atom(b);
    let c_r = RnExpr::Atom(c);
    let pp_r = RnExpr::Atom(pp);
    let qq_r = RnExpr::Atom(qq);
    let rr_r = RnExpr::Atom(rr);
    let z_r = RnExpr::Atom(z);

    let u_r = rn_cevian_u(pp_r.clone(), z_r.clone());
    let v_r = rn_cevian_v(pp_r.clone(), qq_r.clone(), z_r.clone());

    let y_r = rn_lerp(c_r.clone(), a_r.clone(), qq_r.clone());
    let z_pt_r = rn_lerp(a_r.clone(), b_r.clone(), rr_r.clone());

    let lhs_r = rn_lerp(b_r.clone(), y_r, u_r);
    let rhs_main_r = rn_lerp(c_r.clone(), z_pt_r, v_r);

    let d_r = rn_cevian_d(pp_r.clone(), qq_r.clone());
    let dz_minus_one_r = RnExpr::add(RnExpr::mul(d_r, z_r.clone()), RnExpr::neg(RnExpr::One));
    let cb_r = rn_diff(c_r.clone(), b_r.clone());
    let term1_r = RnExpr::mul(dz_minus_one_r, cb_r);

    let ab_r = rn_diff(a_r.clone(), b_r.clone());
    let z_ab_r = RnExpr::mul(z_r, ab_r.clone());
    let defect_r = rn_ceva_defect(pp_r, qq_r, rr_r);
    let term2_r = RnExpr::mul(z_ab_r, defect_r);

    let correction_r = RnExpr::add(term1_r.clone(), term2_r.clone());
    let rhs_full_r = RnExpr::add(rhs_main_r.clone(), correction_r);

    let ring_pf = rn_ring_proof(d, creal, &lhs_r, &rhs_full_r);

    let lhs_actual = rn_render(d, creal, &lhs_r);
    let rhs_main_actual = rn_render(d, creal, &rhs_main_r);
    let term1_actual = rn_render(d, creal, &term1_r);
    let term2_actual = rn_render(d, creal, &term2_r);
    let rhs_full_actual = rn_render(d, creal, &rhs_full_r);
    let ab_actual = rn_render(d, creal, &ab_r);

    (
        lhs_actual,
        rhs_main_actual,
        term1_actual,
        term2_actual,
        rhs_full_actual,
        ab_actual,
        ring_pf,
    )
}

/// From the concurrency hypothesis at ONE coordinate (`hmeet_coord : Equiv
/// lhs_actual rhs_main_actual`, matching [`cevian_by_cz_ring_split`]'s
/// output at this `a, b, c`) and `dz_cancel : Equiv (mul big_d z) one`,
/// derive `Equiv (mul ab_actual defect_actual) zero` -- see the module note
/// above for the two-stage cancellation (`term1` unconditionally, then `z`
/// via `D*z~1`).
#[allow(clippy::too_many_arguments)]
fn ceva_converse_coord(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    pp: ExprId,
    qq: ExprId,
    rr: ExprId,
    z: ExprId,
    big_d: ExprId,
    dz_cancel: ExprId,
    hmeet_coord: ExprId,
) -> (ExprId, ExprId) {
    let creal = p.creal;
    let (
        lhs_actual,
        rhs_main_actual,
        term1_actual,
        term2_actual,
        rhs_full_actual,
        ab_actual,
        ring_pf,
    ) = cevian_by_cz_ring_split(d, p, a, b, c, pp, qq, rr, z);

    // `cb_actual` matches [`cevian_correction_zero`]'s own `diff` shape at
    // this `a, b, c` (see the doc there): mirror it here rather than thread
    // it through the ring-split return, since only [`cevian_correction_zero`]
    // needs the standalone value.
    let neg_b = cneg(d, p, b);
    let cb_actual = cadd(d, p, c, neg_b);
    let (_term1_check, term1_zero) = cevian_correction_zero(d, p, big_d, z, cb_actual, dz_cancel);

    // -- `add term1_actual term2_actual ~ zero`, from `hmeet_coord` + `ring_pf` --
    let symm_hmeet = symm(d, p, lhs_actual, rhs_main_actual, hmeet_coord);
    let rhs_main_to_full = chain(
        d,
        p,
        rhs_main_actual,
        &[(lhs_actual, symm_hmeet), (rhs_full_actual, ring_pf)],
    );
    // rhs_main_to_full : Equiv rhs_main_actual rhs_full_actual
    let symm_main_to_full = symm(d, p, rhs_main_actual, rhs_full_actual, rhs_main_to_full);
    // symm_main_to_full : Equiv rhs_full_actual rhs_main_actual
    let raw_zero = sub_eq_zero_of_equiv(d, p, rhs_full_actual, rhs_main_actual, symm_main_to_full);
    // raw_zero : Equiv (add rhs_full_actual (neg rhs_main_actual)) zero
    let neg_rhs_main_actual = cneg(d, p, rhs_main_actual);
    let raw_actual = cadd(d, p, rhs_full_actual, neg_rhs_main_actual);

    let zero = czero(d, p);
    let sum_terms = cadd(d, p, term1_actual, term2_actual);
    // a tiny 2-atom ring identity: `(rhs_main_actual + sum_terms) -
    // rhs_main_actual ~ sum_terms`, `rhs_main_actual`/`sum_terms` opaque.
    let raw_r = RnExpr::add(
        RnExpr::add(RnExpr::Atom(rhs_main_actual), RnExpr::Atom(sum_terms)),
        RnExpr::neg(RnExpr::Atom(rhs_main_actual)),
    );
    let target_r = RnExpr::Atom(sum_terms);
    let cancel_link = rn_ring_proof(d, creal, &raw_r, &target_r);
    // cancel_link : Equiv raw_actual sum_terms
    let symm_cancel_link = symm(d, p, raw_actual, sum_terms, cancel_link);
    let sum_terms_zero = chain(
        d,
        p,
        sum_terms,
        &[(raw_actual, symm_cancel_link), (zero, raw_zero)],
    );
    // sum_terms_zero : Equiv sum_terms zero

    // -- subtract `term1_actual ~ zero` to get `term2_actual ~ zero` -------
    let symm_term1 = symm(d, p, term1_actual, zero, term1_zero);
    let refl_term2 = refl(d, p, term2_actual);
    let congr_term2 = d.lemma(
        creal.add_congr,
        &[
            zero,
            term1_actual,
            term2_actual,
            term2_actual,
            symm_term1,
            refl_term2,
        ],
    );
    // congr_term2 : Equiv (add zero term2_actual) sum_terms
    let zero_term2 = cadd(d, p, zero, term2_actual);
    let za = zero_add_proof(d, p, term2_actual); // Equiv zero_term2 term2_actual
    let symm_za = symm(d, p, zero_term2, term2_actual, za);
    let term2_zero = chain(
        d,
        p,
        term2_actual,
        &[
            (zero_term2, symm_za),
            (sum_terms, congr_term2),
            (zero, sum_terms_zero),
        ],
    );
    // term2_zero : Equiv term2_actual zero, term2_actual = mul (mul z ab_actual) defect_actual

    // -- cancel the shared `z` factor via `D*z ~ 1` -------------------------
    let defect_actual = rn_render(
        d,
        creal,
        &rn_ceva_defect(RnExpr::Atom(pp), RnExpr::Atom(qq), RnExpr::Atom(rr)),
    );
    let one = d.kernel().const_(creal.one, vec![]);

    let z_ab = cmul(d, p, z, ab_actual);
    let z_ab_defect = cmul(d, p, z_ab, defect_actual); // = term2_actual, by construction
    let d_term2 = cmul(d, p, big_d, z_ab_defect);
    let refl_bigd = refl(d, p, big_d);
    let congr2 = d.lemma(
        creal.mul_congr,
        &[big_d, big_d, z_ab_defect, zero, refl_bigd, term2_zero],
    );
    // congr2 : Equiv d_term2 (mul big_d zero)
    let d_zero = cmul(d, p, big_d, zero);
    let step3 = d.lemma(creal.mul_zero, &[big_d]); // Equiv d_zero zero

    let bd_r = RnExpr::Atom(big_d);
    let z_r = RnExpr::Atom(z);
    let ab_r = RnExpr::Atom(ab_actual);
    let defect_r = RnExpr::Atom(defect_actual);
    let lhs2_r = RnExpr::mul(
        bd_r.clone(),
        RnExpr::mul(RnExpr::mul(z_r.clone(), ab_r.clone()), defect_r.clone()),
    );
    let rhs2_r = RnExpr::mul(RnExpr::mul(bd_r, z_r), RnExpr::mul(ab_r, defect_r));
    let link = rn_ring_proof(d, creal, &lhs2_r, &rhs2_r);
    // link : Equiv d_term2 bd_z_ab_defect

    let bd_z = cmul(d, p, big_d, z);
    let ab_defect = cmul(d, p, ab_actual, defect_actual);
    let bd_z_ab_defect = cmul(d, p, bd_z, ab_defect);

    let refl_ab_defect = refl(d, p, ab_defect);
    let congr1 = d.lemma(
        creal.mul_congr,
        &[bd_z, one, ab_defect, ab_defect, dz_cancel, refl_ab_defect],
    );
    // congr1 : Equiv bd_z_ab_defect (mul one ab_defect)
    let one_ab_defect = cmul(d, p, one, ab_defect);
    let step2 = one_mul_proof(d, p, ab_defect); // Equiv one_ab_defect ab_defect

    let symm_step2 = symm(d, p, one_ab_defect, ab_defect, step2);
    let symm_congr1 = symm(d, p, bd_z_ab_defect, one_ab_defect, congr1);
    let symm_link = symm(d, p, d_term2, bd_z_ab_defect, link);

    let ab_defect_zero = chain(
        d,
        p,
        ab_defect,
        &[
            (one_ab_defect, symm_step2),
            (bd_z_ab_defect, symm_congr1),
            (d_term2, symm_link),
            (d_zero, congr2),
            (zero, step3),
        ],
    );
    // ab_defect_zero : Equiv ab_defect zero, ab_defect = mul ab_actual defect_actual

    (ab_defect_zero, defect_actual)
}

/// From the two per-coordinate facts `Equiv (mul dx defect) zero` / `Equiv
/// (mul dy defect) zero` (`dx := x A - x B`, `dy := y A - y B`) and `hab :
/// PosBound (distSq A B) k2`, derive `Equiv defect zero` -- squaring and
/// summing the two turns them into `distSq A B * defect² ~ 0`; `distSq A B`
/// invertible cancels it to `defect² ~ 0`, and `eq_zero_of_mul_self_zero`
/// finishes. See the module note above [`cevian_by_cz_ring_split`].
#[allow(clippy::too_many_arguments)]
fn ceva_converse_combine(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    ax: ExprId,
    ay: ExprId,
    bx: ExprId,
    by_: ExprId,
    defect_actual: ExprId,
    k2: ExprId,
    hab: ExprId,
    eqx_zero: ExprId,
    eqy_zero: ExprId,
) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let one = d.kernel().const_(creal.one, vec![]);

    let neg_bx = cneg(d, p, bx);
    let dx = cadd(d, p, ax, neg_bx);
    let neg_by = cneg(d, p, by_);
    let dy = cadd(d, p, ay, neg_by);

    let a1 = cmul(d, p, dx, defect_actual);
    let a2 = cmul(d, p, dy, defect_actual);

    // -- square both facts and sum -----------------------------------------
    let a1a1 = cmul(d, p, a1, a1);
    let sq_x = d.lemma(creal.mul_congr, &[a1, zero, a1, zero, eqx_zero, eqx_zero]);
    let zero_zero = cmul(d, p, zero, zero);
    let zz = zero_mul_proof(d, p, zero);
    let sqx_zero = chain(d, p, a1a1, &[(zero_zero, sq_x), (zero, zz)]);

    let a2a2 = cmul(d, p, a2, a2);
    let sq_y = d.lemma(creal.mul_congr, &[a2, zero, a2, zero, eqy_zero, eqy_zero]);
    let sqy_zero = chain(d, p, a2a2, &[(zero_zero, sq_y), (zero, zz)]);

    let sum_sq = cadd(d, p, a1a1, a2a2);
    let congr_sum = d.lemma(
        creal.add_congr,
        &[a1a1, zero, a2a2, zero, sqx_zero, sqy_zero],
    );
    let zero_zero_add = cadd(d, p, zero, zero);
    let az = d.lemma(creal.add_zero, &[zero]);
    let sum_sq_zero = chain(d, p, sum_sq, &[(zero_zero_add, congr_sum), (zero, az)]);

    // -- ring identity: `sum_sq ~ raw_distsq * defect²` ---------------------
    let dxdx = cmul(d, p, dx, dx);
    let dydy = cmul(d, p, dy, dy);
    let raw_distsq = cadd(d, p, dxdx, dydy);
    let dx_r = RnExpr::Atom(dx);
    let dy_r = RnExpr::Atom(dy);
    let defect_r = RnExpr::Atom(defect_actual);
    let lhs_r = RnExpr::add(
        RnExpr::mul(
            RnExpr::mul(dx_r.clone(), defect_r.clone()),
            RnExpr::mul(dx_r.clone(), defect_r.clone()),
        ),
        RnExpr::mul(
            RnExpr::mul(dy_r.clone(), defect_r.clone()),
            RnExpr::mul(dy_r.clone(), defect_r.clone()),
        ),
    );
    let rhs_r = RnExpr::mul(
        RnExpr::add(
            RnExpr::mul(dx_r.clone(), dx_r),
            RnExpr::mul(dy_r.clone(), dy_r),
        ),
        RnExpr::mul(defect_r.clone(), defect_r),
    );
    let ring_link = rn_ring_proof(d, creal, &lhs_r, &rhs_r);
    // ring_link : Equiv sum_sq raw_distsq_defect_sq

    let defect_sq = cmul(d, p, defect_actual, defect_actual);
    let raw_distsq_defect_sq = cmul(d, p, raw_distsq, defect_sq);
    let symm_ring_link = symm(d, p, sum_sq, raw_distsq_defect_sq, ring_link);
    let rd_defect_sq_zero = chain(
        d,
        p,
        raw_distsq_defect_sq,
        &[(sum_sq, symm_ring_link), (zero, sum_sq_zero)],
    );
    // rd_defect_sq_zero : Equiv raw_distsq_defect_sq zero

    // -- invert `raw_distsq` (defeq-bridged against `hab`'s stated type) ---
    let inv_distsq = d.const_app(creal.inv, &[raw_distsq, k2, hab]);
    let mul_inv_cancel_pf = d.lemma(creal.mul_inv_cancel, &[raw_distsq, k2, hab]);
    // mul_inv_cancel_pf : Equiv (mul raw_distsq inv_distsq) one

    let rd_r = RnExpr::Atom(raw_distsq);
    let inv_r = RnExpr::Atom(inv_distsq);
    let ds_r = RnExpr::Atom(defect_sq);
    let lhs2_r = RnExpr::mul(inv_r.clone(), RnExpr::mul(rd_r.clone(), ds_r.clone()));
    let rhs2_r = RnExpr::mul(RnExpr::mul(rd_r, inv_r), ds_r);
    let link2 = rn_ring_proof(d, creal, &lhs2_r, &rhs2_r);
    // link2 : Equiv inv_times_prod rd_inv_ds

    let inv_times_prod = cmul(d, p, inv_distsq, raw_distsq_defect_sq);
    let refl_inv = refl(d, p, inv_distsq);
    let congr3 = d.lemma(
        creal.mul_congr,
        &[
            inv_distsq,
            inv_distsq,
            raw_distsq_defect_sq,
            zero,
            refl_inv,
            rd_defect_sq_zero,
        ],
    );
    // congr3 : Equiv inv_times_prod (mul inv_distsq zero)
    let inv_zero = cmul(d, p, inv_distsq, zero);
    let mz2 = d.lemma(creal.mul_zero, &[inv_distsq]);
    let inv_times_prod_zero = chain(d, p, inv_times_prod, &[(inv_zero, congr3), (zero, mz2)]);

    let rd_inv = cmul(d, p, raw_distsq, inv_distsq);
    let rd_inv_ds = cmul(d, p, rd_inv, defect_sq);
    let symm_link2 = symm(d, p, inv_times_prod, rd_inv_ds, link2);
    let rd_inv_ds_zero = chain(
        d,
        p,
        rd_inv_ds,
        &[(inv_times_prod, symm_link2), (zero, inv_times_prod_zero)],
    );

    let refl_ds = refl(d, p, defect_sq);
    let congr4 = d.lemma(
        creal.mul_congr,
        &[
            rd_inv,
            one,
            defect_sq,
            defect_sq,
            mul_inv_cancel_pf,
            refl_ds,
        ],
    );
    // congr4 : Equiv rd_inv_ds (mul one defect_sq)
    let one_ds = cmul(d, p, one, defect_sq);
    let step_one_mul = one_mul_proof(d, p, defect_sq); // Equiv one_ds defect_sq

    let symm_step_one_mul = symm(d, p, one_ds, defect_sq, step_one_mul);
    let symm_congr4 = symm(d, p, rd_inv_ds, one_ds, congr4);
    let defect_sq_zero = chain(
        d,
        p,
        defect_sq,
        &[
            (one_ds, symm_step_one_mul),
            (rd_inv_ds, symm_congr4),
            (zero, rd_inv_ds_zero),
        ],
    );
    // defect_sq_zero : Equiv defect_sq zero

    d.lemma(
        creal.eq_zero_of_mul_self_zero,
        &[defect_actual, defect_sq_zero],
    )
}

/// **Ceva's theorem, the converse.** See
/// [`CPointPrelude::ceva_ratio_product_of_concurrent`].
fn declare_ceva_ratio_product_of_concurrent(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let rr_fv = d.fresh_fvar();
    let rr = d.kernel().fvar(rr_fv);
    let k_fv = d.fresh_fvar();
    let pk = d.kernel().fvar(k_fv);
    let k2_fv = d.fresh_fvar();
    let pk2 = d.kernel().fvar(k2_fv);

    let big_d = cevian_big_d(d, p, pp, qq);
    let dd = cmul(d, p, big_d, big_d);
    let hd_ty = d.const_app(creal.pos_bound, &[dd, pk]);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let dist_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let hab_ty = d.const_app(creal.pos_bound, &[dist_ab, pk2]);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let z = cevian_dinv(d, p, big_d, pk, hd);
    let dz_cancel = cevian_dinv_cancel(d, p, big_d, pk, hd);

    let u_expr = rn_render(d, creal, &rn_cevian_u(RnExpr::Atom(pp), RnExpr::Atom(z)));
    let v_expr = rn_render(
        d,
        creal,
        &rn_cevian_v(RnExpr::Atom(pp), RnExpr::Atom(qq), RnExpr::Atom(z)),
    );

    let big_y = d.const_app(p.point_lerp, &[pc, pa, qq]);
    let big_z = d.const_app(p.point_lerp, &[pa, pb, rr]);
    let by_point = d.const_app(p.point_lerp, &[pb, big_y, u_expr]);
    let cz_point = d.const_app(p.point_lerp, &[pc, big_z, v_expr]);

    let hmeet_ty = d.const_app(p.point_equiv, &[by_point, cz_point]);
    let hmeet_fv = d.fresh_fvar();
    let hmeet = d.kernel().fvar(hmeet_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by_ = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);

    let by_x = d.const_app(p.x, &[by_point]);
    let cz_x = d.const_app(p.x, &[cz_point]);
    let by_y = d.const_app(p.y, &[by_point]);
    let cz_y = d.const_app(p.y, &[cz_point]);
    let ex_ty = equiv(d, p, by_x, cz_x);
    let ey_ty = equiv(d, p, by_y, cz_y);
    let hmeet_x = d.and_left(ex_ty, ey_ty, hmeet);
    let hmeet_y = d.and_right(ex_ty, ey_ty, hmeet);

    let (ab_defect_zero_x, defect_actual_x) =
        ceva_converse_coord(d, p, ax, bx, cx, pp, qq, rr, z, big_d, dz_cancel, hmeet_x);
    let (ab_defect_zero_y, defect_actual_y) =
        ceva_converse_coord(d, p, ay, by_, cy, pp, qq, rr, z, big_d, dz_cancel, hmeet_y);
    // `defect_actual` depends only on `p, q, r`, so both runs land on the
    // same `ExprId` by construction (interning) -- kept as two names only to
    // document that each run independently computed it, checked mutually
    // below.
    debug_assert_eq!(defect_actual_x, defect_actual_y);

    let defect_zero = ceva_converse_combine(
        d,
        p,
        ax,
        ay,
        bx,
        by_,
        defect_actual_x,
        pk2,
        hab,
        ab_defect_zero_x,
        ab_defect_zero_y,
    );
    // defect_zero : Equiv defect_actual_x zero

    let ceva_lhs_expr = rn_render(
        d,
        creal,
        &rn_ceva_lhs(RnExpr::Atom(pp), RnExpr::Atom(qq), RnExpr::Atom(rr)),
    );
    let ceva_rhs_expr = rn_render(
        d,
        creal,
        &rn_ceva_rhs(RnExpr::Atom(pp), RnExpr::Atom(qq), RnExpr::Atom(rr)),
    );
    let concl_proof = equiv_of_sub_eq_zero(d, p, ceva_lhs_expr, ceva_rhs_expr, defect_zero);
    let concl = equiv(d, p, ceva_lhs_expr, ceva_rhs_expr);

    let ty_body = {
        let inner = d.pi_fv(hmeet_fv, hmeet_ty, concl);
        let w1 = d.pi_fv(hab_fv, hab_ty, inner);
        let w2 = d.pi_fv(hd_fv, hd_ty, w1);
        let w3 = d.pi_fv(k2_fv, nat, w2);
        let w4 = d.pi_fv(k_fv, nat, w3);
        let w5 = d.pi_fv(rr_fv, carrier, w4);
        let w6 = d.pi_fv(qq_fv, carrier, w5);
        d.pi_fv(pp_fv, carrier, w6)
    };
    let ty = {
        let w1 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w1);
        d.pi_fv(a_fv, point, w2)
    };
    let value_body = {
        let inner = d.lam_fv(hmeet_fv, hmeet_ty, concl_proof);
        let w1 = d.lam_fv(hab_fv, hab_ty, inner);
        let w2 = d.lam_fv(hd_fv, hd_ty, w1);
        let w3 = d.lam_fv(k2_fv, nat, w2);
        let w4 = d.lam_fv(k_fv, nat, w3);
        let w5 = d.lam_fv(rr_fv, carrier, w4);
        let w6 = d.lam_fv(qq_fv, carrier, w5);
        d.lam_fv(pp_fv, carrier, w6)
    };
    let value = {
        let w1 = d.lam_fv(c_fv, point, value_body);
        let w2 = d.lam_fv(b_fv, point, w1);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ceva_ratio_product_of_concurrent,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// Heron's formula, squared: the area of a triangle from its three squared
// side lengths, with no `CReal.sqrt` anywhere below (at the time this was
// written the kernel had none; `CReal.sqrt` landed 2026-08-26, and this
// section was never rebuilt around it). See [`CPointPrelude::heron_sixteen_area_sq`]
// for the statement and the reasoning route.
//
// The identity was checked exactly with `Fraction` arithmetic (no `sympy` in
// this environment), 8 independent random rational triangles, zero residual
// every time:
//
//     4*cross(A,B,C)^2 == 4*a2*b2 - (a2+b2-c2)^2
//
// with `a2 = distSq B C, b2 = distSq C A, c2 = distSq A B` -- i.e.
// `16*Area^2 = 4a^2b^2 - (a^2+b^2-c^2)^2`, the standard law-of-cosines form
// of Heron's formula. Both sides expand (by hand, cross-checked against the
// trials) to the symmetric `2a^2b^2 + 2b^2c^2 + 2c^2a^2 - a^4 - b^4 - c^4`,
// so this is the SAME identity regardless of which side plays the odd one
// out -- the statement below is the `a^2b^2`/`(a^2+b^2-c^2)^2` pairing the
// fact ledger's convention names, matching `cross A B C`'s own `(B-A)`,
// `(C-B)` construction directly (no cyclic-permutation lemma needed).
// ============================================================================

/// `Equiv (mul (add x x) (add x x)) (add xx (add xx (add xx xx)))`,
/// `xx := mul x x` -- `(2x)^2 = x^2+x^2+x^2+x^2`, with `x` as ONE opaque
/// atom. Tiny (degree 2, one atom) regardless of what raw structure `x`
/// itself carries, so this is safe to call on a large compound `x`.
fn heron_double_square(d: &mut IntDev<'_>, creal: CRealPrelude, x: ExprId) -> ExprId {
    let lhs = RnExpr::mul(
        RnExpr::add(RnExpr::Atom(x), RnExpr::Atom(x)),
        RnExpr::add(RnExpr::Atom(x), RnExpr::Atom(x)),
    );
    let xx = RnExpr::mul(RnExpr::Atom(x), RnExpr::Atom(x));
    let rhs = RnExpr::add(
        xx.clone(),
        RnExpr::add(xx.clone(), RnExpr::add(xx.clone(), xx)),
    );
    rn_ring_proof(d, creal, &lhs, &rhs)
}

/// Given `h : Equiv x y`, lifts it through 4-fold repeated addition:
/// `Equiv (add x (add x (add x x))) (add y (add y (add y y)))`, via
/// `add_congr` three times. Cheap (no ring-normalizer call) regardless of
/// `x`/`y`'s own size.
fn heron_repeat4(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    let creal = p.creal;
    let h2 = rn_op_congr(d, creal, RnOp::Add, x, y, x, y, h, h);
    let xx = cadd(d, p, x, x);
    let yy = cadd(d, p, y, y);
    let h3 = rn_op_congr(d, creal, RnOp::Add, x, y, xx, yy, h, h2);
    let xxx = cadd(d, p, x, xx);
    let yyy = cadd(d, p, y, yy);
    rn_op_congr(d, creal, RnOp::Add, x, y, xxx, yyy, h, h3)
}

/// See the module note above and [`CPointPrelude::heron_sixteen_area_sq`].
///
/// Built in stages, each individually small, rather than as one flat
/// six-atom degree-4-times-2 ring identity: a first cut at this proof
/// (`4*(cross+cross)... ` fully expanded through `rn_ring_proof` in one
/// shot) overflowed a 64 MiB deep-stack thread during
/// `Kernel::add_declaration` -- the raw monomial count before cancellation
/// runs into the hundreds once `distSq`'s own two-binomial expansion is
/// squared and multiplied out together with `cross`'s.
///
/// The staging routes around that through **two** genuinely small ring
/// facts (each verified exactly with `Fraction` trials before being
/// encoded, zero residual):
///
///   * Fact A: `cross^2 ~ a2*b2 - dot2^2`, `dot2 := (B-C)Â·(A-C)` (raw) --
///     this is exactly Lagrange's identity for the vectors `B-C, A-C`, and
///     unlike the two-vector pairing `cross`'s own `u,v,w,z` naturally
///     produces (`c2*a2`, not `a2*b2`), this one lands on the ledger's own
///     `a2*b2` pairing directly, with **no** extra pairing-conversion
///     lemma needed.
///   * Fact B: `2*dot2 ~ a2 + b2 - c2` -- from `2u.v = |u|^2+|v|^2-|u-v|^2`
///     at `u := B-C, v := A-C, u-v = B-A`.
///
/// The final identity is then assembled from A and B by **congruence and
/// transitivity alone** (`heron_repeat4`, `mul_congr`/`add_congr`,
/// `heron_double_square`) -- no further call to the ring normalizer, so no
/// further blowup risk, regardless of how large `cross`/`distSq`'s own raw
/// forms are.
fn heron_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    ax: ExprId,
    ay: ExprId,
    bx: ExprId,
    by: ExprId,
    cx: ExprId,
    cy: ExprId,
) -> ExprId {
    let creal = p.creal;

    let a2_rn = rn_dist_sq(
        RnExpr::Atom(bx),
        RnExpr::Atom(by),
        RnExpr::Atom(cx),
        RnExpr::Atom(cy),
    );
    let b2_rn = rn_dist_sq(
        RnExpr::Atom(cx),
        RnExpr::Atom(cy),
        RnExpr::Atom(ax),
        RnExpr::Atom(ay),
    );
    let c2_rn = rn_dist_sq(
        RnExpr::Atom(ax),
        RnExpr::Atom(ay),
        RnExpr::Atom(bx),
        RnExpr::Atom(by),
    );
    let a2_val = rn_render(d, creal, &a2_rn);
    let b2_val = rn_render(d, creal, &b2_rn);

    let cross_rn = rn_cross(
        RnExpr::Atom(ax),
        RnExpr::Atom(ay),
        RnExpr::Atom(bx),
        RnExpr::Atom(by),
        RnExpr::Atom(cx),
        RnExpr::Atom(cy),
    );
    let cross_val = rn_render(d, creal, &cross_rn);

    // dot2 := (B-C).(A-C), raw.
    let dot2_rn = RnExpr::add(
        RnExpr::mul(
            rn_diff(RnExpr::Atom(bx), RnExpr::Atom(cx)),
            rn_diff(RnExpr::Atom(ax), RnExpr::Atom(cx)),
        ),
        RnExpr::mul(
            rn_diff(RnExpr::Atom(by), RnExpr::Atom(cy)),
            rn_diff(RnExpr::Atom(ay), RnExpr::Atom(cy)),
        ),
    );
    let dot2_val = rn_render(d, creal, &dot2_rn);

    // Fact A: cross^2 ~ a2*b2 - dot2^2.
    let fact_a = {
        let lhs = RnExpr::mul(cross_rn.clone(), cross_rn);
        let rhs = RnExpr::add(
            RnExpr::mul(a2_rn.clone(), b2_rn.clone()),
            RnExpr::neg(RnExpr::mul(dot2_rn.clone(), dot2_rn.clone())),
        );
        rn_ring_proof(d, creal, &lhs, &rhs)
    };
    let ab_val = cmul(d, p, a2_val, b2_val);
    let dd_val = cmul(d, p, dot2_val, dot2_val);
    let cross_sq_val = cmul(d, p, cross_val, cross_val);
    let neg_dd_val = cneg(d, p, dd_val);
    let rhs_a_val = cadd(d, p, ab_val, neg_dd_val);
    // fact_a : Equiv cross_sq_val rhs_a_val

    // Fact B: 2*dot2 ~ a2 + b2 - c2 =: diff.
    let diff_rn = RnExpr::add(a2_rn, RnExpr::add(b2_rn, RnExpr::neg(c2_rn)));
    let fact_b = {
        let lhs = RnExpr::add(dot2_rn.clone(), dot2_rn.clone());
        rn_ring_proof(d, creal, &lhs, &diff_rn)
    };
    let diff_val = rn_render(d, creal, &diff_rn);
    let two_dot2 = cadd(d, p, dot2_val, dot2_val);
    // fact_b : Equiv two_dot2 diff_val

    // (2*dot2)^2 ~ diff^2, bridged through the repeated-add-of-squares form.
    let diff_sq_val = cmul(d, p, diff_val, diff_val);
    let sq_fact_b = rn_op_congr(
        d,
        creal,
        RnOp::Mul,
        two_dot2,
        diff_val,
        two_dot2,
        diff_val,
        fact_b,
        fact_b,
    );
    // sq_fact_b : Equiv (mul two_dot2 two_dot2) diff_sq_val
    let dbl_sq_dot2 = heron_double_square(d, creal, dot2_val);
    let two_dot2_sq_val = cmul(d, p, two_dot2, two_dot2);
    // dbl_sq_dot2 : Equiv two_dot2_sq_val (dd+dd+dd+dd)
    let dd_val_pair = cadd(d, p, dd_val, dd_val);
    let dd_val_triple = cadd(d, p, dd_val, dd_val_pair);
    let dd4_val = cadd(d, p, dd_val, dd_val_triple);
    let dd4_eq_two_dot2_sq = symm(d, p, two_dot2_sq_val, dd4_val, dbl_sq_dot2);
    let dd4_eq_diffsq = chain(
        d,
        p,
        dd4_val,
        &[
            (two_dot2_sq_val, dd4_eq_two_dot2_sq),
            (diff_sq_val, sq_fact_b),
        ],
    );
    // dd4_eq_diffsq : Equiv dd4_val diff_sq_val

    // 4*cross^2 (repeated-add form) ~ 4*(a2*b2 - dot2^2), from fact_a.
    let rhs_a_val_pair = cadd(d, p, rhs_a_val, rhs_a_val);
    let rhs_a_val_triple = cadd(d, p, rhs_a_val, rhs_a_val_pair);
    let rhs_a4_val = cadd(d, p, rhs_a_val, rhs_a_val_triple);
    let four_cross_sq_eq_rhs_a4 = heron_repeat4(d, p, cross_sq_val, rhs_a_val, fact_a);
    // : Equiv (cross_sq+cross_sq+cross_sq+cross_sq) rhs_a4_val

    // rhs_a4 ~ ab4 + neg(dd4) -- pure regrouping over 2 opaque atoms.
    let ab_val_pair = cadd(d, p, ab_val, ab_val);
    let ab_val_triple = cadd(d, p, ab_val, ab_val_pair);
    let ab4_val = cadd(d, p, ab_val, ab_val_triple);
    let neg_dd4_val = cneg(d, p, dd4_val);
    let ab4_plus_neg_dd4_val = cadd(d, p, ab4_val, neg_dd4_val);
    let regroup4 = {
        let rhs_a_rn = RnExpr::add(RnExpr::Atom(ab_val), RnExpr::neg(RnExpr::Atom(dd_val)));
        let lhs = RnExpr::add(
            rhs_a_rn.clone(),
            RnExpr::add(rhs_a_rn.clone(), RnExpr::add(rhs_a_rn.clone(), rhs_a_rn)),
        );
        let ab_rn = RnExpr::Atom(ab_val);
        let dd_rn = RnExpr::Atom(dd_val);
        let ab4_rn = RnExpr::add(
            ab_rn.clone(),
            RnExpr::add(ab_rn.clone(), RnExpr::add(ab_rn.clone(), ab_rn)),
        );
        let dd4_rn = RnExpr::add(
            dd_rn.clone(),
            RnExpr::add(dd_rn.clone(), RnExpr::add(dd_rn.clone(), dd_rn)),
        );
        let rhs = RnExpr::add(ab4_rn, RnExpr::neg(dd4_rn));
        rn_ring_proof(d, creal, &lhs, &rhs)
    };

    // ab4 + neg(dd4) ~ ab4 + neg(diff_sq), substituting `dd4_eq_diffsq`.
    let neg_dd4_eq_neg_diffsq = d.lemma(creal.neg_congr, &[dd4_val, diff_sq_val, dd4_eq_diffsq]);
    let neg_diffsq_val = cneg(d, p, diff_sq_val);
    let ab4_plus_neg_diffsq_val = cadd(d, p, ab4_val, neg_diffsq_val);
    let ab4_refl = refl(d, p, ab4_val);
    let dd4_to_diffsq = rn_op_congr(
        d,
        creal,
        RnOp::Add,
        ab4_val,
        ab4_val,
        neg_dd4_val,
        neg_diffsq_val,
        ab4_refl,
        neg_dd4_eq_neg_diffsq,
    );

    // ab4 ~ (2*a2)*(2*b2) -- pure regrouping over 2 opaque atoms.
    let two_a2_val = cadd(d, p, a2_val, a2_val);
    let two_b2_val = cadd(d, p, b2_val, b2_val);
    let two_a2_two_b2_val = cmul(d, p, two_a2_val, two_b2_val);
    let dbl_prod_ab = {
        let a2_atom = RnExpr::Atom(a2_val);
        let b2_atom = RnExpr::Atom(b2_val);
        let lhs = RnExpr::mul(
            RnExpr::add(a2_atom.clone(), a2_atom),
            RnExpr::add(b2_atom.clone(), b2_atom),
        );
        let ab_rn = RnExpr::mul(RnExpr::Atom(a2_val), RnExpr::Atom(b2_val));
        let rhs = RnExpr::add(
            ab_rn.clone(),
            RnExpr::add(ab_rn.clone(), RnExpr::add(ab_rn.clone(), ab_rn)),
        );
        rn_ring_proof(d, creal, &lhs, &rhs)
    };
    let two_a2_two_b2_eq_ab4 = symm(d, p, two_a2_two_b2_val, ab4_val, dbl_prod_ab);
    let neg_diffsq_refl = refl(d, p, neg_diffsq_val);
    let ab4_to_two_a2_two_b2 = rn_op_congr(
        d,
        creal,
        RnOp::Add,
        ab4_val,
        two_a2_two_b2_val,
        neg_diffsq_val,
        neg_diffsq_val,
        two_a2_two_b2_eq_ab4,
        neg_diffsq_refl,
    );

    let final_rhs_val = cadd(d, p, two_a2_two_b2_val, neg_diffsq_val);
    let cross_sq_val_pair = cadd(d, p, cross_sq_val, cross_sq_val);
    let cross_sq_val_triple = cadd(d, p, cross_sq_val, cross_sq_val_pair);
    let cross_sq4_val = cadd(d, p, cross_sq_val, cross_sq_val_triple);
    let cross_sq4_to_final_rhs = chain(
        d,
        p,
        cross_sq4_val,
        &[
            (rhs_a4_val, four_cross_sq_eq_rhs_a4),
            (ab4_plus_neg_dd4_val, regroup4),
            (ab4_plus_neg_diffsq_val, dd4_to_diffsq),
            (final_rhs_val, ab4_to_two_a2_two_b2),
        ],
    );

    // Finally, bridge `cross_sq4` back to `(cross+cross)*(cross+cross)`.
    let dbl_sq_cross = heron_double_square(d, creal, cross_val);
    let two_cross_val = cadd(d, p, cross_val, cross_val);
    let two_cross_sq_val = cmul(d, p, two_cross_val, two_cross_val);
    chain(
        d,
        p,
        two_cross_sq_val,
        &[
            (cross_sq4_val, dbl_sq_cross),
            (final_rhs_val, cross_sq4_to_final_rhs),
        ],
    )
}

/// `CPoint.heron_sixteen_area_sq`. See
/// [`CPointPrelude::heron_sixteen_area_sq`].
fn declare_heron_sixteen_area_sq(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
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

    let proof = heron_scalar_proof(d, p, ax, ay, bx, by, cx, cy);

    // The folded, readable type -- `CPoint.cross`/`CPoint.distSq` heads, not
    // raw coordinates. The kernel accepts `proof` against it by delta/iota
    // unfolding those (plus `dot`, `sub`, `x`, `y`) back down to the exact
    // raw shape `proof` was built over -- see `heron_scalar_proof`'s doc for
    // the precedent this depth of unfolding already has in this file.
    let cross_abc = d.const_app(p.cross, &[pa, pb, pc]);
    let double_cross = cadd(d, p, cross_abc, cross_abc);
    let lhs_ty = cmul(d, p, double_cross, double_cross);

    let a2 = d.const_app(p.dist_sq, &[pb, pc]);
    let b2 = d.const_app(p.dist_sq, &[pc, pa]);
    let c2 = d.const_app(p.dist_sq, &[pa, pb]);
    let double_a2 = cadd(d, p, a2, a2);
    let double_b2 = cadd(d, p, b2, b2);
    let neg_c2 = cneg(d, p, c2);
    let b2_minus_c2 = cadd(d, p, b2, neg_c2);
    let diff_ty = cadd(d, p, a2, b2_minus_c2);
    let diff_sq_ty = cmul(d, p, diff_ty, diff_ty);
    let neg_diff_sq_ty = cneg(d, p, diff_sq_ty);
    let ab_ty = cmul(d, p, double_a2, double_b2);
    let rhs_ty = cadd(d, p, ab_ty, neg_diff_sq_ty);

    let ty_body = equiv(d, p, lhs_ty, rhs_ty);
    let ty = {
        let w1 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w1);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let w1 = d.lam_fv(c_fv, point, proof);
        let w2 = d.lam_fv(b_fv, point, w1);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.heron_sixteen_area_sq,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// The triangle-area slice: translation invariance of `cross`, one direction
// of "signed area vanishes iff collinear", and the medial triangle's area.
// See `CPointPrelude::cross_translate`/`collinear`/`area_zero_of_collinear`/
// `medial_triangle_cross_quarter` for the mathematical content; this section
// is only the kernel plumbing.

/// **Translation invariance of `cross`.** See
/// [`CPointPrelude::cross_translate`].
fn declare_cross_translate(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let v_fv = d.fresh_fvar();
    let pv = d.kernel().fvar(v_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);
    let vx = d.const_app(p.x, &[pv]);
    let vy = d.const_app(p.y, &[pv]);

    let ax_r = RnExpr::Atom(ax);
    let ay_r = RnExpr::Atom(ay);
    let bx_r = RnExpr::Atom(bx);
    let by_r = RnExpr::Atom(by);
    let cx_r = RnExpr::Atom(cx);
    let cy_r = RnExpr::Atom(cy);
    let vx_r = RnExpr::Atom(vx);
    let vy_r = RnExpr::Atom(vy);

    let ax_v_r = RnExpr::add(ax_r.clone(), vx_r.clone());
    let ay_v_r = RnExpr::add(ay_r.clone(), vy_r.clone());
    let bx_v_r = RnExpr::add(bx_r.clone(), vx_r.clone());
    let by_v_r = RnExpr::add(by_r.clone(), vy_r.clone());
    let cx_v_r = RnExpr::add(cx_r.clone(), vx_r);
    let cy_v_r = RnExpr::add(cy_r.clone(), vy_r);

    let cross_translated_r = rn_cross(ax_v_r, ay_v_r, bx_v_r, by_v_r, cx_v_r, cy_v_r);
    let cross_abc_r = rn_cross(ax_r, ay_r, bx_r, by_r, cx_r, cy_r);

    let ring_pf = rn_ring_proof(d, creal, &cross_translated_r, &cross_abc_r);

    // -- the theorem's stated conclusion, at the Point level ---------------
    let a_v = padd(d, p, pa, pv);
    let b_v = padd(d, p, pb, pv);
    let c_v = padd(d, p, pc, pv);
    let cross_translated_stated = d.const_app(p.cross, &[a_v, b_v, c_v]);
    let cross_abc_stated = d.const_app(p.cross, &[pa, pb, pc]);
    let ty_body = equiv(d, p, cross_translated_stated, cross_abc_stated);

    let ty = {
        let w1 = d.pi_fv(v_fv, point, ty_body);
        let w2 = d.pi_fv(c_fv, point, w1);
        let w3 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(a_fv, point, w3)
    };
    let value = {
        let w1 = d.lam_fv(v_fv, point, ring_pf);
        let w2 = d.lam_fv(c_fv, point, w1);
        let w3 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w3)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cross_translate,
        uparams: vec![],
        ty,
        value,
    })
}

/// `λ t : CReal, CPoint.Equiv C (CPoint.lerp A B t)` -- the predicate behind
/// [`CPointPrelude::collinear`], built fresh at every call site (never a
/// shared `ExprId`) the same way `creal.rs`'s own `gap_predicate` is: the
/// kernel bridges any two calls' results by delta/beta defeq at the final
/// `add_declaration` check, so they need not be the identical `ExprId`.
fn collinear_predicate(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    pa: ExprId,
    pb: ExprId,
    pc: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let lerp_abt = d.const_app(p.point_lerp, &[pa, pb, t]);
    let body = d.const_app(p.point_equiv, &[pc, lerp_abt]);
    d.lam_fv(t_fv, carrier, body)
}

/// `CPoint.Collinear A B C := Exists CReal (fun t => CPoint.Equiv C (lerp A B
/// t))`. See [`CPointPrelude::collinear`].
fn declare_collinear(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let predicate = collinear_predicate(d, p, pa, pb, pc);
    let exists_name = p.creal.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    let claim = d.apply(exists_const, &[carrier, predicate]);

    let value = {
        let w2 = d.lam_fv(c_fv, point, claim);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    let ty = {
        let w2 = d.arrow(point, prop);
        let w1 = d.arrow(point, w2);
        d.arrow(point, w1)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.collinear,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 20),
    })
}

/// Eliminate `witness : Exists CReal predicate` into `target`, given `minor :
/// ∀ (t : CReal), predicate t → target`. The `CReal`-domain sibling of
/// `int_prelude::ops::exists_elim`, which is hard-coded to the `Nat` domain
/// (see that function's own doc) and so cannot be reused for a `∃ t : CReal,
/// …` hypothesis like [`CPointPrelude::collinear`]'s.
fn exists_elim_creal(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let one = d.level_one();
    let exists_name = p.creal.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    let exists_ty = d.apply(exists_const, &[carrier, predicate]);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, exists_ty, target)
    };
    let rec_name = p.creal.rat.int.logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[carrier, predicate, motive, minor, witness])
}

/// The third-argument congruence of [`CPointPrelude::cross`]: given `hq :
/// CPoint.Equiv Q Q'` (`A`, `B` untouched), a proof of `Equiv (cross_raw ax ay
/// bx by (x Q) (y Q)) (cross_raw ax ay bx by (x Q') (y Q'))`.
///
/// Not itself a public declaration -- `cross` is built directly from `x`/`y`
/// projections (`cross_raw`), not from [`CPointPrelude::dot`]/
/// [`CPointPrelude::point_sub`] the way [`CPointPrelude::dist_sq`] is, so it
/// cannot reuse [`CPointPrelude::dot_congr`] and needs its own small
/// congruence chain -- mirroring `psub_congr_fact`'s role for
/// `declare_dist_sq_congr`.
fn cross_congr_c_fact(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    pa: ExprId,
    pb: ExprId,
    qc: ExprId,
    qc2: ExprId,
    hq: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[qc]);
    let cy = d.const_app(p.y, &[qc]);
    let cx2 = d.const_app(p.x, &[qc2]);
    let cy2 = d.const_app(p.y, &[qc2]);

    let ex_ty = equiv(d, p, cx, cx2);
    let ey_ty = equiv(d, p, cy, cy2);
    let hcx = d.and_left(ex_ty, ey_ty, hq);
    let hcy = d.and_right(ex_ty, ey_ty, hq);

    // u := bx - ax, w := by - ay -- neither depends on C, so both sides share
    // exactly the same `u`/`w`.
    let neg_ax = cneg(d, p, ax);
    let neg_ay = cneg(d, p, ay);
    let u = cadd(d, p, bx, neg_ax);
    let w = cadd(d, p, by, neg_ay);
    let refl_u = refl(d, p, u);
    let refl_w = refl(d, p, w);

    // v := cy - by ~ v' := cy2 - by ; z := cx - bx ~ z' := cx2 - bx.
    let neg_by = cneg(d, p, by);
    let neg_bx = cneg(d, p, bx);
    let v = cadd(d, p, cy, neg_by);
    let v2 = cadd(d, p, cy2, neg_by);
    let z = cadd(d, p, cx, neg_bx);
    let z2 = cadd(d, p, cx2, neg_bx);
    let refl_neg_by = refl(d, p, neg_by);
    let refl_neg_bx = refl(d, p, neg_bx);
    let v_congr = d.lemma(
        creal.add_congr,
        &[cy, cy2, neg_by, neg_by, hcy, refl_neg_by],
    );
    let z_congr = d.lemma(
        creal.add_congr,
        &[cx, cx2, neg_bx, neg_bx, hcx, refl_neg_bx],
    );

    // uv := u*v ~ uv' := u*v'.
    let uv = cmul(d, p, u, v);
    let uv2 = cmul(d, p, u, v2);
    let uv_congr = d.lemma(creal.mul_congr, &[u, u, v, v2, refl_u, v_congr]);

    // wz := w*z ~ wz' := w*z'.
    let wz = cmul(d, p, w, z);
    let wz2 = cmul(d, p, w, z2);
    let wz_congr = d.lemma(creal.mul_congr, &[w, w, z, z2, refl_w, z_congr]);

    let neg_wz_congr = d.lemma(creal.neg_congr, &[wz, wz2, wz_congr]);

    // value := uv + neg wz ~ uv2 + neg wz2 -- cross_raw's own final step.
    let neg_wz = cneg(d, p, wz);
    let neg_wz2 = cneg(d, p, wz2);
    d.lemma(
        creal.add_congr,
        &[uv, uv2, neg_wz, neg_wz2, uv_congr, neg_wz_congr],
    )
}

/// **One direction of "signed area vanishes iff collinear".** See
/// [`CPointPrelude::area_zero_of_collinear`].
fn declare_area_zero_of_collinear(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
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

    let hcol_ty = d.const_app(p.collinear, &[pa, pb, pc]);
    let hcol_fv = d.fresh_fvar();
    let hcol = d.kernel().fvar(hcol_fv);

    // -- minor : ∀ t, CPoint.Equiv C (lerp A B t) → Equiv (cross A B C) zero
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let lerp_abt = d.const_app(p.point_lerp, &[pa, pb, t]);
    let ht_ty = d.const_app(p.point_equiv, &[pc, lerp_abt]);
    let ht_fv = d.fresh_fvar();
    let ht = d.kernel().fvar(ht_fv);

    // cross A B C ~ cross A B (lerp A B t), from `ht` via the 3rd-arg
    // congruence built above.
    let congr_pf = cross_congr_c_fact(d, p, pa, pb, pc, lerp_abt, ht);

    // cross A B (lerp A B t) ~ 0 -- a pure ring identity, no hypothesis: a
    // point on segment AB is always collinear with A, B.
    let ax_r = RnExpr::Atom(ax);
    let ay_r = RnExpr::Atom(ay);
    let bx_r = RnExpr::Atom(bx);
    let by_r = RnExpr::Atom(by);
    let t_r = RnExpr::Atom(t);
    let lerp_x_r = rn_lerp(ax_r.clone(), bx_r.clone(), t_r.clone());
    let lerp_y_r = rn_lerp(ay_r.clone(), by_r.clone(), t_r);
    let cross_ablerp_r = rn_cross(ax_r, ay_r, bx_r, by_r, lerp_x_r, lerp_y_r);
    let ring_pf = rn_ring_proof(d, creal, &cross_ablerp_r, &RnExpr::Zero);

    let cross_abc = d.const_app(p.cross, &[pa, pb, pc]);
    let cross_ablerp = d.const_app(p.cross, &[pa, pb, lerp_abt]);
    let zero = czero(d, p);

    let minor_proof = chain(
        d,
        p,
        cross_abc,
        &[(cross_ablerp, congr_pf), (zero, ring_pf)],
    );
    let minor = {
        let w1 = d.lam_fv(ht_fv, ht_ty, minor_proof);
        d.lam_fv(t_fv, carrier, w1)
    };

    let target = equiv(d, p, cross_abc, zero);
    let predicate = collinear_predicate(d, p, pa, pb, pc);
    let final_proof = exists_elim_creal(d, p, predicate, target, hcol, minor);

    let ty = {
        let inner = d.arrow(hcol_ty, target);
        let w3 = d.pi_fv(c_fv, point, inner);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let with_hcol = d.lam_fv(hcol_fv, hcol_ty, final_proof);
        let w3 = d.lam_fv(c_fv, point, with_hcol);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.area_zero_of_collinear,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The medial triangle's area.** See
/// [`CPointPrelude::medial_triangle_cross_quarter`].
fn declare_medial_triangle_cross_quarter(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
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
    let inv2 = d.kernel().const_(p.inv2, vec![]);

    let ax_r = RnExpr::Atom(ax);
    let ay_r = RnExpr::Atom(ay);
    let bx_r = RnExpr::Atom(bx);
    let by_r = RnExpr::Atom(by);
    let cx_r = RnExpr::Atom(cx);
    let cy_r = RnExpr::Atom(cy);
    let inv2_r = RnExpr::Atom(inv2);

    // `rn_midpoint u v := inv2 * (u + v)`, the `RnExpr` mirror of
    // `CPoint.Scalar.midpoint`'s own `mul inv2 (add a b)` shape.
    let rn_midpoint = |u: RnExpr, v: RnExpr| RnExpr::mul(inv2_r.clone(), RnExpr::add(u, v));

    let max_r = rn_midpoint(bx_r.clone(), cx_r.clone());
    let may_r = rn_midpoint(by_r.clone(), cy_r.clone());
    let mbx_r = rn_midpoint(cx_r.clone(), ax_r.clone());
    let mby_r = rn_midpoint(cy_r.clone(), ay_r.clone());
    let mcx_r = rn_midpoint(ax_r.clone(), bx_r.clone());
    let mcy_r = rn_midpoint(ay_r.clone(), by_r.clone());

    let cross_medial_r = rn_cross(max_r, may_r, mbx_r, mby_r, mcx_r, mcy_r);
    let cross_abc_r = rn_cross(ax_r, ay_r, bx_r, by_r, cx_r, cy_r);
    let quarter_r = RnExpr::mul(inv2_r.clone(), RnExpr::mul(inv2_r, cross_abc_r));

    let ring_pf = rn_ring_proof(d, creal, &cross_medial_r, &quarter_r);

    // -- the theorem's stated conclusion, at the Point level ---------------
    let ma = d.const_app(p.point_midpoint, &[pb, pc]);
    let mb = d.const_app(p.point_midpoint, &[pc, pa]);
    let mc = d.const_app(p.point_midpoint, &[pa, pb]);
    let cross_medial_stated = d.const_app(p.cross, &[ma, mb, mc]);
    let cross_abc_stated = d.const_app(p.cross, &[pa, pb, pc]);
    let inv2_cross_abc_stated = cmul(d, p, inv2, cross_abc_stated);
    let quarter_stated = cmul(d, p, inv2, inv2_cross_abc_stated);
    let ty_body = equiv(d, p, cross_medial_stated, quarter_stated);

    let ty = {
        let w2 = d.pi_fv(c_fv, point, ty_body);
        let w1 = d.pi_fv(b_fv, point, w2);
        d.pi_fv(a_fv, point, w1)
    };
    let value = {
        let w2 = d.lam_fv(c_fv, point, ring_pf);
        let w1 = d.lam_fv(b_fv, point, w2);
        d.lam_fv(a_fv, point, w1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.medial_triangle_cross_quarter,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// `collinear_of_area_zero`: the converse of `area_zero_of_collinear`, under a
// witnessed `A ≠ B`. See `CPointPrelude::collinear_of_area_zero`'s doc for
// the construction on paper; this section is only the kernel plumbing.

/// Given `ring_pf : Equiv (mul v dee) (add (mul s u) (mul factor
/// cross_actual))` (a pure ring identity) and `hcross : Equiv cross_actual
/// CReal.zero`, return `Equiv (mul v dee) (mul s u)` -- the correction term
/// `mul factor cross_actual` collapses to `CReal.zero` and drops out.
#[allow(clippy::too_many_arguments)]
fn eliminate_correction_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    v: ExprId,
    dee: ExprId,
    s: ExprId,
    u: ExprId,
    factor: ExprId,
    cross_actual: ExprId,
    hcross: ExprId,
    ring_pf: ExprId,
) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);

    let factor_cross = cmul(d, p, factor, cross_actual);
    let refl_factor = refl(d, p, factor);
    let step_a = d.lemma(
        creal.mul_congr,
        &[factor, factor, cross_actual, zero, refl_factor, hcross],
    ); // Equiv(factor_cross, mul factor zero)
    let factor_zero = cmul(d, p, factor, zero);
    let mz = d.lemma(creal.mul_zero, &[factor]); // Equiv(factor_zero, zero)
    let factor_cross_zero = chain(d, p, factor_cross, &[(factor_zero, step_a), (zero, mz)]);

    let s_u = cmul(d, p, s, u);
    let su_fc = cadd(d, p, s_u, factor_cross);
    let su_zero = cadd(d, p, s_u, zero);
    let refl_su = refl(d, p, s_u);
    let step_b = d.lemma(
        creal.add_congr,
        &[s_u, s_u, factor_cross, zero, refl_su, factor_cross_zero],
    ); // Equiv(su_fc, su_zero)
    let az = d.lemma(creal.add_zero, &[s_u]); // Equiv(su_zero, s_u)

    let v_d = cmul(d, p, v, dee);
    chain(d, p, v_d, &[(su_fc, ring_pf), (su_zero, step_b), (s_u, az)])
}

/// Given `v_dee_eq_s_u : Equiv (mul v dee) (mul s u)` and `dee_dinv_eq_one :
/// Equiv (mul dee dinv) CReal.one`, return `Equiv v (mul t u)`, `t := mul s
/// dinv` (built by the caller so both share the same `ExprId`).
///
/// The "divide by an invertible `PosBound` witness" step
/// [`CPointPrelude::circumcentre_unique`]'s own proof needs too, factored out
/// here because this theorem needs it TWICE (once per coordinate) with the
/// same `dee`/`dinv`/`t`.
#[allow(clippy::too_many_arguments)]
fn divide_by_pos_bound_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    v: ExprId,
    dee: ExprId,
    s: ExprId,
    u: ExprId,
    dinv: ExprId,
    t: ExprId,
    v_dee_eq_s_u: ExprId,
    dee_dinv_eq_one: ExprId,
) -> ExprId {
    let creal = p.creal;
    let one = d.kernel().const_(creal.one, vec![]);

    // v ~ v*one
    let v_one = cmul(d, p, v, one);
    let mo = d.lemma(creal.mul_one, &[v]); // Equiv(v_one, v)
    let step1 = symm(d, p, v_one, v, mo);

    // v*one ~ v*(dee*dinv)
    let d_dinv = cmul(d, p, dee, dinv);
    let v_ddinv = cmul(d, p, v, d_dinv);
    let refl_v = refl(d, p, v);
    let dee_dinv_symm = symm(d, p, d_dinv, one, dee_dinv_eq_one);
    let step2 = d.lemma(creal.mul_congr, &[v, v, one, d_dinv, refl_v, dee_dinv_symm]); // Equiv(v_one, v_ddinv)

    // v*(dee*dinv) ~ (v*dee)*dinv
    let v_d = cmul(d, p, v, dee);
    let vd_dinv = cmul(d, p, v_d, dinv);
    let assoc1 = d.lemma(creal.mul_assoc, &[v, dee, dinv]); // Equiv(vd_dinv, v_ddinv)
    let assoc1_symm = symm(d, p, vd_dinv, v_ddinv, assoc1);

    // (v*dee)*dinv ~ (s*u)*dinv
    let s_u = cmul(d, p, s, u);
    let su_dinv = cmul(d, p, s_u, dinv);
    let refl_dinv = refl(d, p, dinv);
    let step4 = d.lemma(
        creal.mul_congr,
        &[v_d, s_u, dinv, dinv, v_dee_eq_s_u, refl_dinv],
    ); // Equiv(vd_dinv, su_dinv)

    // (s*u)*dinv ~ s*(u*dinv)
    let u_dinv = cmul(d, p, u, dinv);
    let s_udinv = cmul(d, p, s, u_dinv);
    let assoc2 = d.lemma(creal.mul_assoc, &[s, u, dinv]); // Equiv(su_dinv, s_udinv)

    // s*(u*dinv) ~ s*(dinv*u)
    let dinv_u = cmul(d, p, dinv, u);
    let s_dinvu = cmul(d, p, s, dinv_u);
    let comm_u_dinv = d.lemma(creal.mul_comm, &[u, dinv]); // Equiv(u_dinv, dinv_u)
    let refl_s = refl(d, p, s);
    let step6 = d.lemma(
        creal.mul_congr,
        &[s, s, u_dinv, dinv_u, refl_s, comm_u_dinv],
    ); // Equiv(s_udinv, s_dinvu)

    // s*(dinv*u) ~ (s*dinv)*u = t*u  (t := mul s dinv, so this IS t*u)
    let sdinv_u = cmul(d, p, t, u);
    let assoc3 = d.lemma(creal.mul_assoc, &[s, dinv, u]); // Equiv(sdinv_u, s_dinvu)
    let assoc3_symm = symm(d, p, sdinv_u, s_dinvu, assoc3);

    chain(
        d,
        p,
        v,
        &[
            (v_one, step1),
            (v_ddinv, step2),
            (vd_dinv, assoc1_symm),
            (su_dinv, step4),
            (s_udinv, assoc2),
            (s_dinvu, step6),
            (sdinv_u, assoc3_symm),
        ],
    )
}

/// Given `h : Equiv (add cx (neg ax)) w`, return `Equiv cx (add ax w)` --
/// "isolate `cx`", the inverse rearrangement of [`sub_eq_zero_of_equiv`]'s
/// shape but against an arbitrary `w` rather than `CReal.zero`.
fn isolate_left_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    cx: ExprId,
    ax: ExprId,
    w: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let neg_ax = cneg(d, p, ax);
    let cx_negax = cadd(d, p, cx, neg_ax);
    let cx_negax_ax = cadd(d, p, cx_negax, ax);
    let cancel = sub_add_cancel_proof(d, p, cx, ax); // Equiv(cx_negax_ax, cx)
    let cancel_symm = symm(d, p, cx_negax_ax, cx, cancel);

    let w_ax = cadd(d, p, w, ax);
    let refl_ax = refl(d, p, ax);
    let congr = d.lemma(creal.add_congr, &[cx_negax, w, ax, ax, h, refl_ax]); // Equiv(cx_negax_ax, w_ax)

    let ax_w = cadd(d, p, ax, w);
    let comm = d.lemma(creal.add_comm, &[w, ax]); // Equiv(w_ax, ax_w)

    chain(
        d,
        p,
        cx,
        &[(cx_negax_ax, cancel_symm), (w_ax, congr), (ax_w, comm)],
    )
}

/// **The converse of [`CPointPrelude::area_zero_of_collinear`], under a
/// witnessed `A ≠ B`.** See [`CPointPrelude::collinear_of_area_zero`].
fn declare_collinear_of_area_zero(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let k_fv = d.fresh_fvar();
    let pk = d.kernel().fvar(k_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);

    // -- the two hypotheses --------------------------------------------
    let dist_ab = d.const_app(p.dist_sq, &[pa, pb]);
    let hne_ty = d.const_app(creal.pos_bound, &[dist_ab, pk]);
    let hne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(hne_fv);

    let cross_abc = d.const_app(p.cross, &[pa, pb, pc]);
    let zero = czero(d, p);
    let hcross_ty = equiv(d, p, cross_abc, zero);
    let hcross_fv = d.fresh_fvar();
    let hcross = d.kernel().fvar(hcross_fv);

    // -- raw coordinate machinery ----------------------------------------
    // `u := B - A` (matches `lerp_raw`'s own shape); `v := C - A`; `w := A -
    // B` (matches `distSq A B`'s own raw unfolding, `dot(sub A B, sub A B)`).
    let neg_ax = cneg(d, p, ax);
    let neg_ay = cneg(d, p, ay);
    let neg_bx = cneg(d, p, bx);
    let neg_by = cneg(d, p, by);
    let w1 = cadd(d, p, ax, neg_bx);
    let w2 = cadd(d, p, ay, neg_by);
    let u1 = cadd(d, p, bx, neg_ax);
    let u2 = cadd(d, p, by, neg_ay);
    let v1 = cadd(d, p, cx, neg_ax);
    let v2 = cadd(d, p, cy, neg_ay);

    let w1_sq = cmul(d, p, w1, w1);
    let w2_sq = cmul(d, p, w2, w2);
    let dee = cadd(d, p, w1_sq, w2_sq); // matches distSq A B's raw form
    let v1_u1 = cmul(d, p, v1, u1);
    let v2_u2 = cmul(d, p, v2, u2);
    let s = cadd(d, p, v1_u1, v2_u2); // S := v.u

    let (cross_raw_actual, ..) = cross_raw(d, p, ax, ay, bx, by, cx, cy);

    // -- the two pure ring identities (no hypothesis) --------------------
    let ax_r = RnExpr::Atom(ax);
    let ay_r = RnExpr::Atom(ay);
    let bx_r = RnExpr::Atom(bx);
    let by_r = RnExpr::Atom(by);
    let cx_r = RnExpr::Atom(cx);
    let cy_r = RnExpr::Atom(cy);

    let w1_r = RnExpr::add(ax_r.clone(), RnExpr::neg(bx_r.clone()));
    let w2_r = RnExpr::add(ay_r.clone(), RnExpr::neg(by_r.clone()));
    let u1_r = RnExpr::add(bx_r.clone(), RnExpr::neg(ax_r.clone()));
    let u2_r = RnExpr::add(by_r.clone(), RnExpr::neg(ay_r.clone()));
    let v1_r = RnExpr::add(cx_r.clone(), RnExpr::neg(ax_r.clone()));
    let v2_r = RnExpr::add(cy_r.clone(), RnExpr::neg(ay_r.clone()));
    let dee_r = RnExpr::add(
        RnExpr::mul(w1_r.clone(), w1_r.clone()),
        RnExpr::mul(w2_r.clone(), w2_r.clone()),
    );
    let s_r = RnExpr::add(
        RnExpr::mul(v1_r.clone(), u1_r.clone()),
        RnExpr::mul(v2_r.clone(), u2_r.clone()),
    );
    let cross_r = rn_cross(
        ax_r.clone(),
        ay_r.clone(),
        bx_r.clone(),
        by_r.clone(),
        cx_r.clone(),
        cy_r.clone(),
    );

    // v1*dee ~ s*u1 + (neg u2)*cross
    let lhs1_r = RnExpr::mul(v1_r.clone(), dee_r.clone());
    let rhs1_r = RnExpr::add(
        RnExpr::mul(s_r.clone(), u1_r.clone()),
        RnExpr::mul(RnExpr::neg(u2_r.clone()), cross_r.clone()),
    );
    let ring1_pf = rn_ring_proof(d, creal, &lhs1_r, &rhs1_r);

    // v2*dee ~ s*u2 + u1*cross
    let lhs2_r = RnExpr::mul(v2_r, dee_r);
    let rhs2_r = RnExpr::add(RnExpr::mul(s_r, u2_r), RnExpr::mul(u1_r, cross_r));
    let ring2_pf = rn_ring_proof(d, creal, &lhs2_r, &rhs2_r);

    // -- eliminate the correction term in each, using `hcross` -----------
    let neg_u2 = cneg(d, p, u2);
    let v1_dee_eq_s_u1 = eliminate_correction_proof(
        d,
        p,
        v1,
        dee,
        s,
        u1,
        neg_u2,
        cross_raw_actual,
        hcross,
        ring1_pf,
    );
    let v2_dee_eq_s_u2 =
        eliminate_correction_proof(d, p, v2, dee, s, u2, u1, cross_raw_actual, hcross, ring2_pf);

    // -- divide by the witnessed-invertible `distSq A B` ------------------
    let dinv = d.const_app(creal.inv, &[dist_ab, pk, hne]);
    let t = cmul(d, p, s, dinv);
    let dee_dinv_eq_one = d.lemma(creal.mul_inv_cancel, &[dist_ab, pk, hne]);

    let v1_eq_t_u1 = divide_by_pos_bound_proof(
        d,
        p,
        v1,
        dist_ab,
        s,
        u1,
        dinv,
        t,
        v1_dee_eq_s_u1,
        dee_dinv_eq_one,
    );
    let v2_eq_t_u2 = divide_by_pos_bound_proof(
        d,
        p,
        v2,
        dist_ab,
        s,
        u2,
        dinv,
        t,
        v2_dee_eq_s_u2,
        dee_dinv_eq_one,
    );

    // -- isolate Cx, Cy: Equiv(Cx, Ax + t*u1) = Equiv(Cx, x(lerp A B t)) ---
    let t_u1 = cmul(d, p, t, u1);
    let t_u2 = cmul(d, p, t, u2);
    let hc_x = isolate_left_proof(d, p, cx, ax, t_u1, v1_eq_t_u1);
    let hc_y = isolate_left_proof(d, p, cy, ay, t_u2, v2_eq_t_u2);

    let lerp_x = lerp_raw(d, p, ax, bx, t); // == cadd(ax, t_u1)
    let lerp_y = lerp_raw(d, p, ay, by, t); // == cadd(ay, t_u2)
    let ex_ty = equiv(d, p, cx, lerp_x);
    let ey_ty = equiv(d, p, cy, lerp_y);
    let h_point_equiv = and_intro(d, p, ex_ty, ey_ty, hc_x, hc_y);

    // -- package the witness: Exists.intro CReal predicate t h_point_equiv
    // (`h_point_equiv`'s stated type, `Equiv cx (lerp_raw ax bx t)`, is
    // exactly `predicate`'s body beta/delta-unfolded at this `t` -- `x
    // (CPoint.lerp A B t)` reduces to `lerp_raw (x A) (x B) t` the same way
    // every other `lerp`-headed theorem in this file relies on.)
    let predicate = collinear_predicate(d, p, pa, pb, pc);
    let one = d.level_one();
    let exists_intro_name = creal.rat.int.logic.exists_intro;
    let exists_intro_const = d.kernel().const_(exists_intro_name, vec![one]);
    let collinear_witness = d.apply(exists_intro_const, &[carrier, predicate, t, h_point_equiv]);

    // -- assemble the theorem ---------------------------------------------
    let collinear_ty = d.const_app(p.collinear, &[pa, pb, pc]);
    let ty = {
        let inner = d.arrow(hcross_ty, collinear_ty);
        let with_hne = d.arrow(hne_ty, inner);
        let with_k = d.pi_fv(k_fv, nat, with_hne);
        let with_c = d.pi_fv(c_fv, point, with_k);
        let with_b = d.pi_fv(b_fv, point, with_c);
        d.pi_fv(a_fv, point, with_b)
    };
    let value = {
        let with_hcross = d.lam_fv(hcross_fv, hcross_ty, collinear_witness);
        let with_hne = d.lam_fv(hne_fv, hne_ty, with_hcross);
        let with_k = d.lam_fv(k_fv, nat, with_hne);
        let with_c = d.lam_fv(c_fv, point, with_k);
        let with_b = d.lam_fv(b_fv, point, with_c);
        d.lam_fv(a_fv, point, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.collinear_of_area_zero,
        uparams: vec![],
        ty,
        value,
    })
}

mod angle;
mod isometry;

#[cfg(test)]
mod creal_point_tests;
