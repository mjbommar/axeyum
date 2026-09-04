//! `RN.*` — **ℝⁿ as a carrier**: the finite-dimensional real inner-product
//! space, built once at symbolic dimension rather than once per dimension.
//!
//! Roadmap W2-4 (convergence point C7), ADR-1606. Before this module the
//! library had exactly two real vector spaces, both at a FIXED dimension:
//! `CPoint` (the plane, `creal_point.rs`) and `Complex` (ℝ², under a different
//! multiplication). Everything proved about them — the inner product,
//! Cauchy–Schwarz, the triangle inequality — was written out coordinate by
//! coordinate and generalized to nothing. `Rat.dotN` (`rat_prelude::vector`)
//! is the one n-dimensional inner product in the tree, and it is over ℚ, which
//! has no square root and so cannot carry a norm at all.
//!
//! ## The carrier, and why it is a function and not a tuple
//!
//! **A vector is a coefficient function `Nat → CReal` together with an
//! explicit dimension bound, and the dimension lives in the EQUIVALENCE
//! RELATION rather than in the type.**
//!
//! ```text
//! RN.Vec  : Sort 1                 := Nat → CReal
//! RN.EqOn : Nat → Vec → Vec → Prop := fun n u v => forall i, Nat.lt i n -> CReal.Equiv (u i) (v i)
//! ```
//!
//! So "ℝⁿ" is not one type but one *setoid per `n`* over a single carrier —
//! `(RN.Vec, RN.EqOn n)` — and `RN.metric n` is the metric space it carries.
//! Two vectors that agree below `n` ARE the same point of ℝⁿ no matter what
//! they do above it, which is exactly the quotient a dependent tuple type
//! would have given, obtained without one.
//!
//! The three alternatives, and why each is out (ADR-1606 has the full record):
//!
//! - **`Fin n → CReal`.** `Fin` does not exist in this kernel. Building it
//!   needs either a `Subtype` (`{ i : Nat // i < n }`) or a fresh indexed
//!   inductive family; **there is no `Subtype` and no `Sigma`/`PSigma` here**,
//!   so the subtype route is not available at all, and the indexed-family
//!   route buys a bound-carrying index type whose only use would be to
//!   re-derive the `Nat.lt i n` hypothesis `EqOn` already carries.
//! - **A length-indexed vector (`Vect n`).** Same objection plus a worse one:
//!   every operation becomes a recursor application over the length index, so
//!   `dot`, `add` and `smul` stop being ordinary function composition and
//!   every congruence needs a transport. `CReal.sumRange` — the finite sum
//!   this whole module is built on — is already `Nat.rec` on a BOUND, so a
//!   length-indexed carrier would be fighting the one primitive it needs.
//! - **A `Nat → CReal` with values forced to `zero` above `n`.** That is a
//!   different setoid (ℝ^ω with a support condition), it needs a decidable
//!   comparison inside every definition, and it makes [`RNPrelude::of_cpoint`]
//!   an `if`-expression instead of two `Nat.rec` branches.
//!
//! `Rat.dotN`'s own doc records this decision for ℚ in one line — "this kernel
//! has no product/tuple type, so a vector is not reified as its own carrier"
//! — and this module is the same decision carried to ℝ, where it additionally
//! has to support a norm and hence a `Metric` instance.
//!
//! ## What is proved
//!
//! - The setoid (`eqOn_refl`/`eqOn_symm`/`eqOn_trans`) and the abelian-group
//!   structure (`add`/`neg`/`sub`/`smul` with congruences and the four laws),
//!   every one of them stated **up to `EqOn n`**, never up to `Eq`.
//! - The inner product [`RNPrelude::dot`] with symmetry, bilinearity
//!   (`dot_add_left`/`dot_add_right`/`dot_smul_left`), positive
//!   semidefiniteness (`dot_self_nonneg`) and the setoid congruence
//!   `dot_congr`.
//! - [`RNPrelude::cauchy_schwarz`] — **Cauchy–Schwarz in the UNSQUARED form**,
//!   `<u,v> ≤ ‖u‖·‖v‖`, at symbolic dimension. `Rat.dotN_cauchy_schwarz` and
//!   `CPoint.cauchy_schwarz` are both squared; the unsquared form needs a
//!   square root, and its proof here is a **generalization of
//!   `Metric.CPoint.dotLeSqrtMul`** rather than a rebuild: the induction step
//!   at dimension `n+1` is literally one application of that plane lemma, at
//!   the two points `(‖u‖ₙ, uₙ)` and `(‖v‖ₙ, vₙ)`. See
//!   [`declare_cauchy_schwarz`].
//! - [`RNPrelude::norm_add_le`] (Minkowski) and hence
//!   [`RNPrelude::metric_inst`] — ℝⁿ as a `Metric` instance for **every** `n`,
//!   so `Metric.dist_self`, `Metric.dist_quadrilateral`, `Metric.Cauchy`,
//!   `Metric.TendsTo` and `Metric.Complete` all apply to it without further
//!   work.
//! - The bridge to the plane: [`RNPrelude::of_cpoint`] with agreement on
//!   `dot`, `distSq` and `Metric.CPoint.dist`, and the equivalence transported
//!   in **both** directions (`ofCPoint_congr` / `cpointEquiv_of_eqOn`), which
//!   makes `CPoint` a provable instance of the n = 2 case rather than a
//!   parallel construction.
//!
//! ## What this module does NOT do
//!
//! It does not restate Cauchy–Schwarz in squared form (`<u,v>² ≤ <u,u><v,v>`).
//! That needs `|<u,v>| ≤ ‖u‖‖v‖`, i.e. the bound at `-v` as well as at `v`,
//! and `CReal` has neither `neg_add` nor `mul_neg` as named laws — both exist
//! only as unnamed inline steps inside `creal.rs`. See ADR-1606.

// `RNPrelude` is a `Copy` handle carrying `MetricPrelude` (itself the whole
// `CPointPrelude` and `CRealPrelude`) plus this module's own names, so it is
// large and every `declare_*` below trips `large_types_passed_by_value`. Same
// shape, same suppression and the same reason as `creal.rs`, `creal_point.rs`
// and `metric.rs`: these are long, straight-line term constructions and the
// handle is a `Copy` snapshot by design.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::MetricPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;

/// Delta heights. Everything here sits ABOVE `creal_point.rs`'s band (900-910)
/// and `creal.rs`'s (40s-50s), so an `RN` definition unfolds before anything it
/// is built from -- which is what makes the `dot`/`norm`/`dist` reduction
/// probes close by `Equiv.refl`.
const H_VEC: u16 = 950;
const H_OPS: u16 = 951;
const H_DOT: u16 = 952;
const H_NORM: u16 = 953;
const H_DIST: u16 = 954;
const H_INST: u16 = 955;

/// The interned names produced by [`build_rn_prelude`].
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RNPrelude {
    /// The metric-space record and the plane, and through them the reals.
    pub metric: MetricPrelude,

    // --- `CReal` facts this module needed and `creal.rs` does not name ------
    /// `RN.CReal.negUnique : forall s t, Equiv (add s t) zero -> Equiv t (neg s)`.
    pub creal_neg_unique: NameId,
    /// `RN.CReal.eqOfSubZero : forall a b, Equiv (add a (neg b)) zero -> Equiv a b`.
    pub creal_eq_of_sub_zero: NameId,
    /// `RN.CReal.zeroAdd : forall a, Equiv (add zero a) a`.
    pub creal_zero_add: NameId,
    /// `RN.CReal.rightDistrib : forall a b c,
    /// Equiv (mul (add a b) c) (add (mul a c) (mul b c))`.
    pub creal_right_distrib: NameId,
    /// `RN.CReal.addNonneg : forall a b, le zero a -> le zero b -> le zero (add a b)`.
    pub creal_add_nonneg: NameId,
    /// `RN.CReal.negSub : forall a b, Equiv (add b (neg a)) (neg (add a (neg b)))`.
    pub creal_neg_sub: NameId,
    /// `RN.CReal.sumRangeCongrLt : forall f g n,
    /// (forall i, Nat.lt i n -> Equiv (f i) (g i)) ->
    /// Equiv (sumRange f n) (sumRange g n)` — the **bound-restricted** finite-sum
    /// congruence. `CReal.sumRange_congr` demands agreement at EVERY index; a
    /// setoid whose equality is `EqOn n` supplies it only below `n`, so this is
    /// the form every `RN` congruence actually consumes. Two applications of
    /// `CReal.sumRange_le` closed by `CReal.equiv_of_le_le` — no new induction.
    pub creal_sum_range_congr_lt: NameId,
    /// `RN.CReal.sumRangeZeroConst : forall n, Equiv (sumRange (fun _ => zero) n) zero`.
    pub creal_sum_range_zero_const: NameId,
    /// `RN.CReal.sumRangeNonneg : forall f n, (forall j, le zero (f j)) ->
    /// le zero (sumRange f n)`.
    pub creal_sum_range_nonneg: NameId,
    /// `RN.CReal.sumRangeTermZero : forall f n, (forall j, le zero (f j)) ->
    /// Equiv (sumRange f n) zero -> forall i, Nat.lt i n -> Equiv (f i) zero` — a
    /// finite sum of nonnegative terms that vanishes has every term below the
    /// bound vanish. The one place this module needs `Nat.lt_or_eq_of_le`, and
    /// the whole content of the metric record's `distEquiv` field.
    pub creal_sum_range_term_zero: NameId,

    // --- the carrier -------------------------------------------------------
    /// `RN.Vec : Sort 1 := Nat -> CReal`.
    pub vec: NameId,
    /// `RN.EqOn : Nat -> Vec -> Vec -> Prop
    /// := fun n u v => forall i, Nat.lt i n -> CReal.Equiv (u i) (v i)`.
    ///
    /// **This, not `Eq`, is equality in ℝⁿ**, and it is only ever as good as
    /// `CReal.Equiv` itself. The dimension is a parameter OF THE RELATION.
    pub eq_on: NameId,
    /// `RN.eqOn_refl : forall n u, EqOn n u u`.
    pub eq_on_refl: NameId,
    /// `RN.eqOn_symm : forall n u v, EqOn n u v -> EqOn n v u`.
    pub eq_on_symm: NameId,
    /// `RN.eqOn_trans : forall n u v w, EqOn n u v -> EqOn n v w -> EqOn n u w`.
    pub eq_on_trans: NameId,

    // --- the vector-space operations ---------------------------------------
    /// `RN.zero : Vec := fun _ => CReal.zero`.
    pub zero: NameId,
    /// `RN.add : Vec -> Vec -> Vec := fun u v i => CReal.add (u i) (v i)`.
    pub add: NameId,
    /// `RN.neg : Vec -> Vec := fun u i => CReal.neg (u i)`.
    pub neg: NameId,
    /// `RN.sub : Vec -> Vec -> Vec
    /// := fun u v i => CReal.add (u i) (CReal.neg (v i))`.
    pub sub: NameId,
    /// `RN.smul : CReal -> Vec -> Vec := fun a u i => CReal.mul a (u i)`.
    pub smul: NameId,
    /// `RN.add_congr : forall n u u' v v', EqOn n u u' -> EqOn n v v' ->
    /// EqOn n (add u v) (add u' v')`.
    pub add_congr: NameId,
    /// `RN.sub_congr : forall n u u' v v', EqOn n u u' -> EqOn n v v' ->
    /// EqOn n (sub u v) (sub u' v')`.
    pub sub_congr: NameId,
    /// `RN.smul_congr : forall n a a' u u', CReal.Equiv a a' -> EqOn n u u' ->
    /// EqOn n (smul a u) (smul a' u')`.
    pub smul_congr: NameId,
    /// `RN.add_comm : forall n u v, EqOn n (add u v) (add v u)`.
    pub add_comm: NameId,
    /// `RN.add_assoc : forall n u v w, EqOn n (add (add u v) w) (add u (add v w))`.
    pub add_assoc: NameId,
    /// `RN.add_zero : forall n u, EqOn n (add u zero) u`.
    pub add_zero: NameId,
    /// `RN.add_neg : forall n u, EqOn n (add u (neg u)) zero`.
    pub add_neg: NameId,

    // --- the inner product -------------------------------------------------
    /// `RN.dot : Vec -> Vec -> Nat -> CReal
    /// := fun u v n => CReal.sumRange (fun i => CReal.mul (u i) (v i)) n`.
    ///
    /// Argument order matches `Rat.dotN` (vectors first, bound last) so the two
    /// n-dimensional inner products in the tree read the same way.
    pub dot: NameId,
    /// `RN.dot_zero : forall u v, Equiv (dot u v Nat.zero) CReal.zero` — `Equiv.refl`.
    pub dot_zero: NameId,
    /// `RN.dot_succ : forall u v n, Equiv (dot u v (Nat.succ n))
    /// (add (dot u v n) (mul (u n) (v n)))` — `Equiv.refl`.
    pub dot_succ: NameId,
    /// `RN.dot_comm : forall u v n, Equiv (dot u v n) (dot v u n)`.
    pub dot_comm: NameId,
    /// `RN.dot_congr : forall n u u' v v', EqOn n u u' -> EqOn n v v' ->
    /// Equiv (dot u v n) (dot u' v' n)` — the fact that makes `dot` a function
    /// on the SETOID rather than on representatives.
    pub dot_congr: NameId,
    /// `RN.dot_add_left : forall a b v n,
    /// Equiv (dot (add a b) v n) (add (dot a v n) (dot b v n))`.
    pub dot_add_left: NameId,
    /// `RN.dot_add_right : forall u a b n,
    /// Equiv (dot u (add a b) n) (add (dot u a n) (dot u b n))`.
    pub dot_add_right: NameId,
    /// `RN.dot_smul_left : forall w u v n,
    /// Equiv (dot (smul w u) v n) (mul w (dot u v n))`.
    pub dot_smul_left: NameId,
    /// `RN.dot_self_nonneg : forall u n, le zero (dot u u n)` — positive
    /// semidefiniteness, by induction on the bound out of `CReal.sq_nonneg`.
    pub dot_self_nonneg: NameId,
    /// `RN.dot_two : forall u v, Equiv (dot u v 2)
    /// (add (mul (u 0) (v 0)) (mul (u 1) (v 1)))` — the n = 2 cross-check that
    /// the general recursion collapses to the plane's hand-written formula,
    /// the same role `Rat.dotN_two` plays for ℚ.
    pub dot_two: NameId,

    // --- the norm ----------------------------------------------------------
    /// `RN.norm : Vec -> Nat -> CReal := fun u n => CReal.sqrt (dot u u n)`.
    pub norm: NameId,
    /// `RN.norm_nonneg : forall u n, le zero (norm u n)`.
    pub norm_nonneg: NameId,
    /// `RN.norm_sq : forall u n, Equiv (mul (norm u n) (norm u n)) (dot u u n)`.
    pub norm_sq: NameId,
    /// `RN.norm_congr : forall n u u', EqOn n u u' -> Equiv (norm u n) (norm u' n)`.
    pub norm_congr: NameId,
    /// `RN.cauchy_schwarz : forall u v n, le (dot u v n) (mul (norm u n) (norm v n))`
    /// — **Cauchy–Schwarz, UNSQUARED, at symbolic dimension.** See
    /// [`declare_cauchy_schwarz`] for why the induction step is one
    /// application of `Metric.CPoint.dotLeSqrtMul`.
    pub cauchy_schwarz: NameId,
    /// `RN.norm_add_le : forall u v n,
    /// le (norm (add u v) n) (add (norm u n) (norm v n))` — Minkowski.
    pub norm_add_le: NameId,

    // --- the metric --------------------------------------------------------
    /// `RN.dist : Nat -> Vec -> Vec -> CReal := fun n u v => norm (sub u v) n`.
    pub dist: NameId,
    /// `RN.dist_congr : forall n u u' v v', EqOn n u u' -> EqOn n v v' ->
    /// Equiv (dist n u v) (dist n u' v')`.
    pub dist_congr: NameId,
    /// `RN.dist_nonneg : forall n u v, le zero (dist n u v)`.
    pub dist_nonneg: NameId,
    /// `RN.dist_self : forall n u v, EqOn n u v -> Equiv (dist n u v) zero`.
    pub dist_self: NameId,
    /// `RN.dist_eqOn : forall n u v, Equiv (dist n u v) zero -> EqOn n u v` — the
    /// identity of indiscernibles, in the direction that carries the content.
    pub dist_eq_on: NameId,
    /// `RN.dist_comm : forall n u v, Equiv (dist n u v) (dist n v u)`.
    pub dist_comm: NameId,
    /// `RN.dist_triangle : forall n a b c,
    /// le (dist n a c) (add (dist n a b) (dist n b c))`.
    pub dist_triangle: NameId,
    /// `RN.metric : Nat -> Metric` — **ℝⁿ as a metric space, for every `n` at
    /// once.** Everything `metric.rs` states for an arbitrary `Metric` now
    /// applies to it.
    pub metric_inst: NameId,
    /// `RN.metric_dist : forall n u v,
    /// Equiv (Metric.dist (RN.metric n) u v) (RN.dist n u v)` — the reduction
    /// probe, by `Equiv.refl`.
    pub metric_dist: NameId,

    // --- the bridge to the plane -------------------------------------------
    /// `RN.ofCPoint : CPoint -> Vec` — `x P` at index `0`, `y P` at every
    /// successor. Two `Nat.rec` branches, no decidable comparison; indices
    /// above `1` are irrelevant because equality at n = 2 is `EqOn 2`.
    pub of_cpoint: NameId,
    /// `RN.ofCPoint_dot : forall P Q,
    /// Equiv (dot (ofCPoint P) (ofCPoint Q) 2) (CPoint.dot P Q)`.
    pub of_cpoint_dot: NameId,
    /// `RN.ofCPoint_distSq : forall P Q,
    /// Equiv (dot (sub (ofCPoint P) (ofCPoint Q)) (sub (ofCPoint P) (ofCPoint Q)) 2)
    /// (CPoint.distSq P Q)`.
    pub of_cpoint_dist_sq: NameId,
    /// `RN.ofCPoint_dist : forall P Q,
    /// Equiv (RN.dist 2 (ofCPoint P) (ofCPoint Q)) (Metric.CPoint.dist P Q)` —
    /// the n = 2 instance and `Metric.cpoint` measure the same distance.
    pub of_cpoint_dist: NameId,
    /// `RN.ofCPoint_congr : forall P Q, CPoint.Equiv P Q -> EqOn 2 (ofCPoint P) (ofCPoint Q)`.
    pub of_cpoint_congr: NameId,
    /// `RN.cpointEquiv_of_eqOn : forall P Q,
    /// EqOn 2 (ofCPoint P) (ofCPoint Q) -> CPoint.Equiv P Q` — the converse, so
    /// `ofCPoint` is a setoid EMBEDDING and not merely a map.
    pub cpoint_equiv_of_eq_on: NameId,
}

fn intern(kernel: &mut Kernel, metric: MetricPrelude) -> RNPrelude {
    let root = kernel.anon();
    let rn = kernel.name_str(root, "RN");
    let creal_ns = kernel.name_str(rn, "CReal");

    RNPrelude {
        metric,
        creal_neg_unique: kernel.name_str(creal_ns, "negUnique"),
        creal_eq_of_sub_zero: kernel.name_str(creal_ns, "eqOfSubZero"),
        creal_zero_add: kernel.name_str(creal_ns, "zeroAdd"),
        creal_right_distrib: kernel.name_str(creal_ns, "rightDistrib"),
        creal_add_nonneg: kernel.name_str(creal_ns, "addNonneg"),
        creal_neg_sub: kernel.name_str(creal_ns, "negSub"),
        creal_sum_range_congr_lt: kernel.name_str(creal_ns, "sumRangeCongrLt"),
        creal_sum_range_zero_const: kernel.name_str(creal_ns, "sumRangeZeroConst"),
        creal_sum_range_nonneg: kernel.name_str(creal_ns, "sumRangeNonneg"),
        creal_sum_range_term_zero: kernel.name_str(creal_ns, "sumRangeTermZero"),

        vec: kernel.name_str(rn, "Vec"),
        eq_on: kernel.name_str(rn, "EqOn"),
        eq_on_refl: kernel.name_str(rn, "eqOn_refl"),
        eq_on_symm: kernel.name_str(rn, "eqOn_symm"),
        eq_on_trans: kernel.name_str(rn, "eqOn_trans"),

        zero: kernel.name_str(rn, "zero"),
        add: kernel.name_str(rn, "add"),
        neg: kernel.name_str(rn, "neg"),
        sub: kernel.name_str(rn, "sub"),
        smul: kernel.name_str(rn, "smul"),
        add_congr: kernel.name_str(rn, "add_congr"),
        sub_congr: kernel.name_str(rn, "sub_congr"),
        smul_congr: kernel.name_str(rn, "smul_congr"),
        add_comm: kernel.name_str(rn, "add_comm"),
        add_assoc: kernel.name_str(rn, "add_assoc"),
        add_zero: kernel.name_str(rn, "add_zero"),
        add_neg: kernel.name_str(rn, "add_neg"),

        dot: kernel.name_str(rn, "dot"),
        dot_zero: kernel.name_str(rn, "dot_zero"),
        dot_succ: kernel.name_str(rn, "dot_succ"),
        dot_comm: kernel.name_str(rn, "dot_comm"),
        dot_congr: kernel.name_str(rn, "dot_congr"),
        dot_add_left: kernel.name_str(rn, "dot_add_left"),
        dot_add_right: kernel.name_str(rn, "dot_add_right"),
        dot_smul_left: kernel.name_str(rn, "dot_smul_left"),
        dot_self_nonneg: kernel.name_str(rn, "dot_self_nonneg"),
        dot_two: kernel.name_str(rn, "dot_two"),

        norm: kernel.name_str(rn, "norm"),
        norm_nonneg: kernel.name_str(rn, "norm_nonneg"),
        norm_sq: kernel.name_str(rn, "norm_sq"),
        norm_congr: kernel.name_str(rn, "norm_congr"),
        cauchy_schwarz: kernel.name_str(rn, "cauchy_schwarz"),
        norm_add_le: kernel.name_str(rn, "norm_add_le"),

        dist: kernel.name_str(rn, "dist"),
        dist_congr: kernel.name_str(rn, "dist_congr"),
        dist_nonneg: kernel.name_str(rn, "dist_nonneg"),
        dist_self: kernel.name_str(rn, "dist_self"),
        dist_eq_on: kernel.name_str(rn, "dist_eqOn"),
        dist_comm: kernel.name_str(rn, "dist_comm"),
        dist_triangle: kernel.name_str(rn, "dist_triangle"),
        metric_inst: kernel.name_str(rn, "metric"),
        metric_dist: kernel.name_str(rn, "metric_dist"),

        of_cpoint: kernel.name_str(rn, "ofCPoint"),
        of_cpoint_dot: kernel.name_str(rn, "ofCPoint_dot"),
        of_cpoint_dist_sq: kernel.name_str(rn, "ofCPoint_distSq"),
        of_cpoint_dist: kernel.name_str(rn, "ofCPoint_dist"),
        of_cpoint_congr: kernel.name_str(rn, "ofCPoint_congr"),
        cpoint_equiv_of_eq_on: kernel.name_str(rn, "cpointEquiv_of_eqOn"),
    }
}

/// Run each `declare_*` step in order and **name the one the kernel refused**.
///
/// `KernelError::DeclarationValueMismatch` carries two bare `ExprId`s and no
/// label, so a bare `?` chain turns one rejection into a bisect over fifty-odd
/// declarations at several minutes a build. This prints the step's own
/// identifier and the two types it disagreed about before propagating.
macro_rules! declare_each {
    ($d:expr, $c:expr, $p:expr, [$($step:ident),+ $(,)?]) => {
        $(
            if let Err(err) = $step($d, $c, $p) {
                let detail = match &err {
                    KernelError::DeclarationValueMismatch { declared, inferred } => format!(
                        "\n  declared: {}\n  inferred: {}",
                        $d.kernel().render_lean(*declared),
                        $d.kernel().render_lean(*inferred)
                    ),
                    other => format!("\n  {other:?}"),
                };
                eprintln!("RN: `{}` was refused by the kernel:{detail}", stringify!($step));
                return Err(err);
            }
        )+
    };
}

/// Build (or return, if already built) the `RN.*` declarations.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub fn build_rn_prelude(kernel: &mut Kernel) -> Result<RNPrelude, KernelError> {
    let metric = crate::build_metric_prelude(kernel)?;
    let p = intern(kernel, metric);
    if kernel.environment().get(p.vec).is_some() {
        return Ok(p);
    }
    let c = metric.cpoint.creal;
    let mut d = IntDev::new(kernel, c.rat.int);

    // Every step is named on rejection. `DeclarationValueMismatch` carries two
    // bare `ExprId`s and nothing else, so without the label a refusal here is a
    // bisect over fifty-odd declarations at several minutes a build.
    declare_each!(
        &mut d,
        c,
        p,
        [
            declare_creal_zero_add,
            declare_creal_right_distrib,
            declare_creal_add_nonneg,
            declare_creal_neg_unique,
            declare_creal_eq_of_sub_zero,
            declare_creal_neg_sub,
            declare_creal_sum_range_congr_lt,
            declare_creal_sum_range_zero_const,
            declare_creal_sum_range_nonneg,
            declare_creal_sum_range_term_zero,
            declare_vec,
            declare_eq_on,
            declare_eq_on_refl,
            declare_eq_on_symm,
            declare_eq_on_trans,
            declare_zero,
            declare_add,
            declare_neg,
            declare_sub,
            declare_smul,
            declare_add_congr,
            declare_sub_congr,
            declare_smul_congr,
            declare_group_laws,
            declare_dot,
            declare_dot_zero,
            declare_dot_succ,
            declare_dot_comm,
            declare_dot_congr,
            declare_dot_add_left,
            declare_dot_add_right,
            declare_dot_smul_left,
            declare_dot_self_nonneg,
            declare_dot_two,
            declare_norm,
            declare_norm_nonneg,
            declare_norm_sq,
            declare_norm_congr,
            declare_cauchy_schwarz,
            declare_norm_add_le,
            declare_dist,
            declare_dist_congr,
            declare_dist_nonneg,
            declare_dist_self,
            declare_dist_eq_on,
            declare_dist_comm,
            declare_dist_triangle,
            declare_metric_instance,
            declare_metric_dist,
            declare_of_cpoint,
            declare_of_cpoint_dot,
            declare_of_cpoint_dist_sq,
            declare_of_cpoint_dist,
            declare_of_cpoint_congr,
            declare_cpoint_equiv_of_eq_on,
        ]
    );

    Ok(p)
}

// ---------------------------------------------------------------------------
// `CReal` term/proof shorthands. Every one is a constant applied to arguments;
// none introduces a new estimate. Same set as `metric.rs`'s, kept local so
// that file stays untouched (another lane owns it).
// ---------------------------------------------------------------------------

fn rty(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.creal, vec![])
}
fn rzero(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.zero, vec![])
}
fn radd(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.add, &[a, b])
}
fn rneg(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(c.neg, &[a])
}
fn rmul(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.mul, &[a, b])
}
fn rsqrt(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(c.sqrt, &[a])
}
fn rle(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.le, &[a, b])
}
fn req(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.equiv, &[a, b])
}
fn rrefl(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(c.equiv_refl, &[a])
}
fn rsymm(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(c.equiv_symm, &[a, b, h])
}
fn rtrans(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    a: ExprId,
    b: ExprId,
    e: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    d.lemma(c.equiv_trans, &[a, b, e, h1, h2])
}

/// Left-to-right `Equiv` chain: `(final term, proof that start ~ final)`.
fn rchain(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> (ExprId, ExprId) {
    let mut cur = start;
    let mut acc: Option<ExprId> = None;
    for &(next, step) in steps {
        acc = Some(match acc {
            None => step,
            Some(prev) => rtrans(d, c, start, cur, next, prev, step),
        });
        cur = next;
    }
    let proof = match acc {
        Some(pr) => pr,
        None => rrefl(d, c, start),
    };
    (cur, proof)
}

fn theorem(d: &mut IntDev<'_>, name: NameId, ty: ExprId, value: ExprId) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

fn definition(
    d: &mut IntDev<'_>,
    name: NameId,
    ty: ExprId,
    value: ExprId,
    height: u16,
) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(height),
    })
}

/// The expression `RN.Vec`.
fn vec_ty(d: &mut IntDev<'_>, p: RNPrelude) -> ExprId {
    d.kernel().const_(p.vec, vec![])
}

/// `CReal.sumRange f n`.
fn rsum(d: &mut IntDev<'_>, c: CRealPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(c.sum_range, &[f, n])
}

// ===========================================================================
// The `CReal` gap-fillers.
// ===========================================================================

/// `RN.CReal.zeroAdd : forall a, Equiv (add zero a) a`.
///
/// `creal.rs` names `add_zero` (right unit) and `add_comm` but no left unit;
/// every finite sum in this file starts at `sumRange f 0 = zero` and so needs
/// one. `add_comm` then `add_zero`.
fn declare_creal_zero_add(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let z = rzero(d, c);

    let za = radd(d, c, z, a);
    let az = radd(d, c, a, z);
    let h1 = d.lemma(c.add_comm, &[z, a]); // Equiv (0 + a) (a + 0)
    let h2 = d.lemma(c.add_zero, &[a]); // Equiv (a + 0) a
    let (_, body) = rchain(d, c, za, &[(az, h1), (a, h2)]);

    let ty = {
        let concl = req(d, c, za, a);
        d.pi_fv(a_fv, carrier, concl)
    };
    let value = d.lam_fv(a_fv, carrier, body);
    theorem(d, p.creal_zero_add, ty, value)
}

/// `RN.CReal.rightDistrib : forall a b e,
/// Equiv (mul (add a b) e) (add (mul a e) (mul b e))`.
///
/// `creal.rs` names only `left_distrib`; `mul_comm` on each of the three
/// products turns one into the other.
fn declare_creal_right_distrib(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let ab = radd(d, c, a, b);
    let lhs = rmul(d, c, ab, e);
    let swapped = rmul(d, c, e, ab);
    let ea = rmul(d, c, e, a);
    let eb = rmul(d, c, e, b);
    let dist = radd(d, c, ea, eb);
    let ae = rmul(d, c, a, e);
    let be = rmul(d, c, b, e);
    let rhs = radd(d, c, ae, be);

    let s1 = d.lemma(c.mul_comm, &[ab, e]); // (a+b)·e ~ e·(a+b)
    let s2 = d.lemma(c.left_distrib, &[e, a, b]); // e·(a+b) ~ e·a + e·b
    let ca = d.lemma(c.mul_comm, &[e, a]);
    let cb = d.lemma(c.mul_comm, &[e, b]);
    let s3 = d.lemma(c.add_congr, &[ea, ae, eb, be, ca, cb]);
    let (_, body) = rchain(d, c, lhs, &[(swapped, s1), (dist, s2), (rhs, s3)]);

    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(e_fv, carrier, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(e_fv, carrier, body);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_right_distrib, ty, value)
}

/// `RN.CReal.addNonneg : forall a b, le zero a -> le zero b -> le zero (add a b)`.
fn declare_creal_add_nonneg(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let z = rzero(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let ha_ty = rle(d, c, z, a);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let hb_ty = rle(d, c, z, b);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let zz = radd(d, c, z, z);
    let ab = radd(d, c, a, b);
    let step = d.lemma(c.add_le_add, &[z, a, z, b, ha, hb]); // le (0+0) (a+b)
    let ez = d.lemma(c.add_zero, &[z]); // Equiv (0+0) 0
    let refl_ab = rrefl(d, c, ab);
    let body = d.lemma(c.le_congr, &[zz, z, ab, ab, ez, refl_ab, step]);

    let ty = {
        let concl = rle(d, c, z, ab);
        let t = d.arrow(hb_ty, concl);
        let t = d.arrow(ha_ty, t);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(hb_fv, hb_ty, body);
        let t = d.lam_fv(ha_fv, ha_ty, t);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_add_nonneg, ty, value)
}

/// `RN.CReal.negUnique : forall s t, Equiv (add s t) zero -> Equiv t (neg s)`.
///
/// Uniqueness of the additive inverse: `t ~ 0 + t ~ (-s + s) + t ~ -s + (s + t)
/// ~ -s + 0 ~ -s`. Four named laws, no analysis. `creal_point.rs` has the
/// right-cancellation sibling (`CPoint.add_right_cancel`) but it is stated over
/// the plane's own helpers, not reusable here.
fn declare_creal_neg_unique(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let z = rzero(d, c);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let h_ty = {
        let st = radd(d, c, s, t);
        req(d, c, st, z)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let ns = rneg(d, c, s);
    let st = radd(d, c, s, t);
    let zt = radd(d, c, z, t);
    let sns = radd(d, c, s, ns);
    let nss = radd(d, c, ns, s);
    let nss_t = radd(d, c, nss, t);
    let ns_st = radd(d, c, ns, st);
    let ns_z = radd(d, c, ns, z);

    // t ~ 0 + t
    let za = d.lemma(p.creal_zero_add, &[t]); // Equiv (0+t) t
    let s1 = rsymm(d, c, zt, t, za);
    // 0 + t ~ (-s + s) + t
    let sn = d.lemma(c.add_neg, &[s]); // Equiv (s + -s) 0
    let cm = d.lemma(c.add_comm, &[ns, s]); // Equiv (-s + s) (s + -s)
    let nss_zero = rtrans(d, c, nss, sns, z, cm, sn); // Equiv (-s+s) 0
    let nss_zero_symm = rsymm(d, c, nss, z, nss_zero);
    let refl_t = rrefl(d, c, t);
    let s2 = d.lemma(c.add_congr, &[z, nss, t, t, nss_zero_symm, refl_t]);
    // (-s + s) + t ~ -s + (s + t)
    let s3 = d.lemma(c.add_assoc, &[ns, s, t]);
    // -s + (s + t) ~ -s + 0
    let refl_ns = rrefl(d, c, ns);
    let s4 = d.lemma(c.add_congr, &[ns, ns, st, z, refl_ns, h]);
    // -s + 0 ~ -s
    let s5 = d.lemma(c.add_zero, &[ns]);

    let (_, body) = rchain(
        d,
        c,
        t,
        &[(zt, s1), (nss_t, s2), (ns_st, s3), (ns_z, s4), (ns, s5)],
    );

    let ty = {
        let concl = req(d, c, t, ns);
        let t0 = d.arrow(h_ty, concl);
        let t0 = d.pi_fv(t_fv, carrier, t0);
        d.pi_fv(s_fv, carrier, t0)
    };
    let value = {
        let t0 = d.lam_fv(h_fv, h_ty, body);
        let t0 = d.lam_fv(t_fv, carrier, t0);
        d.lam_fv(s_fv, carrier, t0)
    };
    theorem(d, p.creal_neg_unique, ty, value)
}

/// `RN.CReal.eqOfSubZero : forall a b, Equiv (add a (neg b)) zero -> Equiv a b`.
///
/// `a ~ a + 0 ~ a + (-b + b) ~ (a + -b) + b ~ 0 + b ~ b`.
fn declare_creal_eq_of_sub_zero(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let z = rzero(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let nb = rneg(d, c, b);
    let sub = radd(d, c, a, nb);
    let h_ty = req(d, c, sub, z);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let az = radd(d, c, a, z);
    let bnb = radd(d, c, b, nb);
    let nbb = radd(d, c, nb, b);
    let a_nbb = radd(d, c, a, nbb);
    let sub_b = radd(d, c, sub, b);
    let zb = radd(d, c, z, b);

    // a ~ a + 0
    let az_fwd = d.lemma(c.add_zero, &[a]);
    let s1 = rsymm(d, c, az, a, az_fwd);
    // a + 0 ~ a + (-b + b)
    let bn = d.lemma(c.add_neg, &[b]); // Equiv (b + -b) 0
    let cm = d.lemma(c.add_comm, &[nb, b]); // Equiv (-b + b) (b + -b)
    let nbb_zero = rtrans(d, c, nbb, bnb, z, cm, bn);
    let nbb_zero_symm = rsymm(d, c, nbb, z, nbb_zero);
    let refl_a = rrefl(d, c, a);
    let s2 = d.lemma(c.add_congr, &[a, a, z, nbb, refl_a, nbb_zero_symm]);
    // a + (-b + b) ~ (a + -b) + b
    let assoc_fwd = d.lemma(c.add_assoc, &[a, nb, b]);
    let s3 = rsymm(d, c, sub_b, a_nbb, assoc_fwd);
    // (a + -b) + b ~ 0 + b
    let refl_b = rrefl(d, c, b);
    let s4 = d.lemma(c.add_congr, &[sub, z, b, b, h, refl_b]);
    // 0 + b ~ b
    let s5 = d.lemma(p.creal_zero_add, &[b]);

    let (_, body) = rchain(
        d,
        c,
        a,
        &[(az, s1), (a_nbb, s2), (sub_b, s3), (zb, s4), (b, s5)],
    );

    let ty = {
        let concl = req(d, c, a, b);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_eq_of_sub_zero, ty, value)
}

/// `RN.CReal.negSub : forall a b, Equiv (add b (neg a)) (neg (add a (neg b)))`.
///
/// `b - a` is the additive inverse of `a - b`, via [`RNPrelude::creal_neg_unique`]
/// on the pure abelian-group rearrangement `(a + -b) + (b + -a) ~ 0`. This is
/// what `dist_comm` needs and what `creal.rs` never names.
fn declare_creal_neg_sub(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let z = rzero(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let na = rneg(d, c, a);
    let nb = rneg(d, c, b);
    let s = radd(d, c, a, nb); // a - b
    let t = radd(d, c, b, na); // b - a
    let sum = radd(d, c, s, t);

    // (a + -b) + (b + -a) ~ a + (-b + (b + -a))
    let e1 = d.lemma(c.add_assoc, &[a, nb, t]);
    let inner_term = radd(d, c, nb, t);
    let a_rest = radd(d, c, a, inner_term);
    // -b + (b + -a) ~ (-b + b) + -a
    let nbb = radd(d, c, nb, b);
    let nbb_na = radd(d, c, nbb, na);
    let inner_assoc_fwd = d.lemma(c.add_assoc, &[nb, b, na]);
    let inner_assoc = rsymm(d, c, nbb_na, inner_term, inner_assoc_fwd);
    // (-b + b) ~ 0
    let bnb = radd(d, c, b, nb);
    let bn = d.lemma(c.add_neg, &[b]);
    let cm = d.lemma(c.add_comm, &[nb, b]);
    let nbb_zero = rtrans(d, c, nbb, bnb, z, cm, bn);
    let refl_na = rrefl(d, c, na);
    let z_na = radd(d, c, z, na);
    let to_z_na = d.lemma(c.add_congr, &[nbb, z, na, na, nbb_zero, refl_na]);
    let za_to_na = d.lemma(p.creal_zero_add, &[na]);
    let (_, inner_proof) = rchain(
        d,
        c,
        inner_term,
        &[(nbb_na, inner_assoc), (z_na, to_z_na), (na, za_to_na)],
    );
    // a + (-b + (b + -a)) ~ a + -a ~ 0
    let refl_a = rrefl(d, c, a);
    let a_na = radd(d, c, a, na);
    let e2 = d.lemma(c.add_congr, &[a, a, inner_term, na, refl_a, inner_proof]);
    let e3 = d.lemma(c.add_neg, &[a]);
    let (_, sum_zero) = rchain(d, c, sum, &[(a_rest, e1), (a_na, e2), (z, e3)]);

    let body = d.lemma(p.creal_neg_unique, &[s, t, sum_zero]);

    let ty = {
        let ns = rneg(d, c, s);
        let concl = req(d, c, t, ns);
        let t0 = d.pi_fv(b_fv, carrier, concl);
        d.pi_fv(a_fv, carrier, t0)
    };
    let value = {
        let t0 = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, t0)
    };
    theorem(d, p.creal_neg_sub, ty, value)
}

/// `RN.CReal.sumRangeCongrLt : forall f g n,
/// (forall i, Nat.lt i n -> Equiv (f i) (g i)) -> Equiv (sumRange f n) (sumRange g n)`.
fn declare_creal_sum_range_congr_lt(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rty(d, c);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hyp_ty = pointwise_lt_equiv(d, c, f, g, n);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let sf = rsum(d, c, f, n);
    let sg = rsum(d, c, g, n);

    // forall i, lt i n -> le (f i) (g i)
    let fwd = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let step = d.apply(h, &[i, hi]);
        let body = d.lemma(c.le_of_equiv, &[fi, gi, step]);
        let inner = d.lam_fv(hi_fv, lt_ty, body);
        d.lam_fv(i_fv, nat, inner)
    };
    let bwd = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let step = d.apply(h, &[i, hi]);
        let sym = rsymm(d, c, fi, gi, step);
        let body = d.lemma(c.le_of_equiv, &[gi, fi, sym]);
        let inner = d.lam_fv(hi_fv, lt_ty, body);
        d.lam_fv(i_fv, nat, inner)
    };
    let le1 = d.lemma(c.sum_range_le, &[f, g, n, fwd]);
    let le2 = d.lemma(c.sum_range_le, &[g, f, n, bwd]);
    let body = d.lemma(c.equiv_of_le_le, &[sf, sg, le1, le2]);

    let ty = {
        let concl = req(d, c, sf, sg);
        let t = d.arrow(hyp_ty, concl);
        let t = d.pi_fv(n_fv, nat, t);
        let t = d.pi_fv(g_fv, fn_ty, t);
        d.pi_fv(f_fv, fn_ty, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, body);
        let t = d.lam_fv(n_fv, nat, t);
        let t = d.lam_fv(g_fv, fn_ty, t);
        d.lam_fv(f_fv, fn_ty, t)
    };
    theorem(d, p.creal_sum_range_congr_lt, ty, value)
}

/// `Nat.lt a b`.
fn nat_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let name = d.prelude().lt;
    d.const_app(name, &[a, b])
}

/// `forall i, Nat.lt i n -> CReal.Equiv (f i) (g i)`.
fn pointwise_lt_equiv(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    f: ExprId,
    g: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let lt_ty = nat_lt(d, i, n);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let eqv = req(d, c, fi, gi);
    let inner = d.arrow(lt_ty, eqv);
    d.pi_fv(i_fv, nat, inner)
}

/// `forall j, CReal.le CReal.zero (f j)`.
fn pointwise_nonneg(d: &mut IntDev<'_>, c: CRealPrelude, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let z = rzero(d, c);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let fj = d.apply(f, &[j]);
    let body = rle(d, c, z, fj);
    d.pi_fv(j_fv, nat, body)
}

/// The constant-zero summand `fun _ => CReal.zero`.
fn zero_fn(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let z = rzero(d, c);
    let i_fv = d.fresh_fvar();
    d.lam_fv(i_fv, nat, z)
}

/// `RN.CReal.sumRangeZeroConst : forall n, Equiv (sumRange (fun _ => zero) n) zero`.
fn declare_creal_sum_range_zero_const(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let z = rzero(d, c);
    let f = zero_fn(d, c);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let s = rsum(d, c, f, x);
        req(d, c, s, z)
    };
    let stmt = motive(d, n);
    let proof = d.induct(
        &motive,
        &|d| rrefl(d, c, z),
        &|d, j, ih| {
            // sumRange f (succ j) = sumRange f j + zero
            let prior = rsum(d, c, f, j);
            let sum = radd(d, c, prior, z);
            let zz = radd(d, c, z, z);
            let refl_z = rrefl(d, c, z);
            let s1 = d.lemma(c.add_congr, &[prior, z, z, z, ih, refl_z]);
            let s2 = d.lemma(c.add_zero, &[z]);
            let (_, pr) = rchain(d, c, sum, &[(zz, s1), (z, s2)]);
            pr
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    theorem(d, p.creal_sum_range_zero_const, ty, value)
}

/// `RN.CReal.sumRangeNonneg : forall f n, (forall j, le zero (f j)) ->
/// le zero (sumRange f n)`.
fn declare_creal_sum_range_nonneg(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rty(d, c);
    let fn_ty = d.arrow(nat, carrier);
    let z = rzero(d, c);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hyp_ty = pointwise_nonneg(d, c, f);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let s = rsum(d, c, f, x);
        rle(d, c, z, s)
    };
    let stmt = motive(d, n);
    let proof = d.induct(
        &motive,
        &|d| d.lemma(c.le_refl, &[z]),
        &|d, j, ih| {
            let prior = rsum(d, c, f, j);
            let fj = d.apply(f, &[j]);
            let hj = d.apply(h, &[j]);
            d.lemma(p.creal_add_nonneg, &[prior, fj, ih, hj])
        },
        n,
    );

    let ty = {
        let t = d.arrow(hyp_ty, stmt);
        let t = d.pi_fv(n_fv, nat, t);
        d.pi_fv(f_fv, fn_ty, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, proof);
        let t = d.lam_fv(n_fv, nat, t);
        d.lam_fv(f_fv, fn_ty, t)
    };
    theorem(d, p.creal_sum_range_nonneg, ty, value)
}

/// `RN.CReal.sumRangeTermZero : forall f n, (forall j, le zero (f j)) ->
/// Equiv (sumRange f n) zero -> forall i, Nat.lt i n -> Equiv (f i) zero`.
///
/// Induction on the bound. The step splits `sumRange f (succ j) ~ 0` with
/// `CReal.eq_zero_of_add_eq_zero_of_nonneg` (which `creal.rs` already has, in
/// both slots via `add_comm`), and then splits `Nat.lt i (succ j)` with
/// `Nat.le_of_lt_succ` + `Nat.lt_or_eq_of_le` — the only case analysis in this
/// module.
fn declare_creal_sum_range_term_zero(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rty(d, c);
    let fn_ty = d.arrow(nat, carrier);
    let z = rzero(d, c);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hyp_ty = pointwise_nonneg(d, c, f);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // motive x := Equiv (sumRange f x) zero -> forall i, lt i x -> Equiv (f i) zero
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let s = rsum(d, c, f, x);
        let ante = req(d, c, s, z);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, x);
        let fi = d.apply(f, &[i]);
        let concl = req(d, c, fi, z);
        let inner = d.arrow(lt_ty, concl);
        let all_i = d.pi_fv(i_fv, nat, inner);
        d.arrow(ante, all_i)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            // No index is below zero: `Nat.not_lt_zero` then `False.elim`.
            let zero_n = d.zero();
            let s0 = rsum(d, c, f, zero_n);
            let ante_ty = req(d, c, s0, z);
            let ha_fv = d.fresh_fvar();
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_ty = nat_lt(d, i, zero_n);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let fi = d.apply(f, &[i]);
            let target = req(d, c, fi, z);
            let not_lt = d.prelude().not_lt_zero;
            let contradiction = d.const_app(not_lt, &[i, hi]);
            let body = d.absurd(target, contradiction);
            let t = d.lam_fv(hi_fv, lt_ty, body);
            let t = d.lam_fv(i_fv, nat, t);
            d.lam_fv(ha_fv, ante_ty, t)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let s_succ = rsum(d, c, f, sj);
            let ante_ty = req(d, c, s_succ, z);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);

            let prior = rsum(d, c, f, j);
            let fj = d.apply(f, &[j]);
            let hj = d.apply(h, &[j]);
            let prior_nonneg = d.lemma(p.creal_sum_range_nonneg, &[f, j, h]);

            // sumRange f j ~ 0
            let ha_reduced = {
                // `ha : Equiv (sumRange f (succ j)) zero`, and that term is
                // definitionally `add (sumRange f j) (f j)`.
                ha
            };
            let split_left = d.lemma(
                c.eq_zero_of_add_eq_zero_of_nonneg,
                &[prior, fj, prior_nonneg, hj, ha_reduced],
            );
            // f j ~ 0, by commuting the sum first.
            let sum_fwd = radd(d, c, prior, fj);
            let sum_bwd = radd(d, c, fj, prior);
            let comm = d.lemma(c.add_comm, &[fj, prior]);
            let ha_swapped = rtrans(d, c, sum_bwd, sum_fwd, z, comm, ha_reduced);
            let split_right = d.lemma(
                c.eq_zero_of_add_eq_zero_of_nonneg,
                &[fj, prior, hj, prior_nonneg, ha_swapped],
            );

            let rest = d.apply(ih, &[split_left]);

            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_ty = nat_lt(d, i, sj);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let fi = d.apply(f, &[i]);
            let target = req(d, c, fi, z);

            let le_name = d.prelude().le_of_lt_succ;
            let le_i_j = d.const_app(le_name, &[i, j, hi]);
            let split_name = d.prelude().lt_or_eq_of_le;
            let disj = d.const_app(split_name, &[i, j, le_i_j]);
            let lt_case = nat_lt(d, i, j);
            let eq_case = d.eq(i, j);
            let branch = d.or_elim(
                lt_case,
                eq_case,
                target,
                disj,
                &|d, hlt| d.apply(rest, &[i, hlt]),
                &|d, heq| {
                    let back = d.symm(i, j, heq);
                    d.nat_rewrite(j, i, back, split_right, &|d, x| {
                        let fx = d.apply(f, &[x]);
                        req(d, c, fx, z)
                    })
                },
            );

            let t = d.lam_fv(hi_fv, lt_ty, branch);
            let t = d.lam_fv(i_fv, nat, t);
            d.lam_fv(ha_fv, ante_ty, t)
        },
        n,
    );

    let ty = {
        let t = d.arrow(hyp_ty, stmt);
        let t = d.pi_fv(n_fv, nat, t);
        d.pi_fv(f_fv, fn_ty, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, proof);
        let t = d.lam_fv(n_fv, nat, t);
        d.lam_fv(f_fv, fn_ty, t)
    };
    theorem(d, p.creal_sum_range_term_zero, ty, value)
}

// ===========================================================================
// The carrier and its setoid.
// ===========================================================================

/// `RN.EqOn n u v`.
fn eq_on(d: &mut IntDev<'_>, p: RNPrelude, n: ExprId, u: ExprId, v: ExprId) -> ExprId {
    d.const_app(p.eq_on, &[n, u, v])
}

/// `RN.dot u v n`.
fn dot(d: &mut IntDev<'_>, p: RNPrelude, u: ExprId, v: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.dot, &[u, v, n])
}

/// `RN.norm u n`.
fn norm(d: &mut IntDev<'_>, p: RNPrelude, u: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.norm, &[u, n])
}

/// `RN.add u v`.
fn vadd(d: &mut IntDev<'_>, p: RNPrelude, u: ExprId, v: ExprId) -> ExprId {
    d.const_app(p.add, &[u, v])
}

/// `RN.sub u v`.
fn vsub(d: &mut IntDev<'_>, p: RNPrelude, u: ExprId, v: ExprId) -> ExprId {
    d.const_app(p.sub, &[u, v])
}

/// `RN.dist n u v`.
fn vdist(d: &mut IntDev<'_>, p: RNPrelude, n: ExprId, u: ExprId, v: ExprId) -> ExprId {
    d.const_app(p.dist, &[n, u, v])
}

/// `RN.Vec : Sort 1 := Nat -> CReal`.
fn declare_vec(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rty(d, c);
    let value = d.arrow(nat, carrier);
    let l0 = d.kernel().level_zero();
    let l1 = d.kernel().level_succ(l0);
    let ty = d.kernel().sort(l1);
    definition(d, p.vec, ty, value, H_VEC)
}

/// `RN.EqOn : Nat -> Vec -> Vec -> Prop`.
fn declare_eq_on(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let body = pointwise_lt_equiv(d, c, u, v, n);
    let value = {
        let t = d.lam_fv(v_fv, vec, body);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    let ty = {
        let l0 = d.kernel().level_zero();
        let prop = d.kernel().sort(l0);
        let t = d.arrow(vec, prop);
        let t = d.arrow(vec, t);
        d.arrow(nat, t)
    };
    definition(d, p.eq_on, ty, value, H_OPS)
}

/// `RN.eqOn_refl : forall n u, EqOn n u u`.
fn declare_eq_on_refl(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let body = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let ui = d.apply(u, &[i]);
        let pr = rrefl(d, c, ui);
        let t = d.lam_fv(hi_fv, lt_ty, pr);
        d.lam_fv(i_fv, nat, t)
    };
    let ty = {
        let concl = eq_on(d, p, n, u, u);
        let t = d.pi_fv(u_fv, vec, concl);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(u_fv, vec, body);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.eq_on_refl, ty, value)
}

/// `RN.eqOn_symm : forall n u v, EqOn n u v -> EqOn n v u`.
fn declare_eq_on_symm(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let h_ty = eq_on(d, p, n, u, v);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let body = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let step = d.apply(h, &[i, hi]);
        let pr = rsymm(d, c, ui, vi, step);
        let t = d.lam_fv(hi_fv, lt_ty, pr);
        d.lam_fv(i_fv, nat, t)
    };
    let ty = {
        let concl = eq_on(d, p, n, v, u);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(v_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(v_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.eq_on_symm, ty, value)
}

/// `RN.eqOn_trans : forall n u v w, EqOn n u v -> EqOn n v w -> EqOn n u w`.
fn declare_eq_on_trans(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let h1_ty = eq_on(d, p, n, u, v);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = eq_on(d, p, n, v, w);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let body = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let wi = d.apply(w, &[i]);
        let s1 = d.apply(h1, &[i, hi]);
        let s2 = d.apply(h2, &[i, hi]);
        let pr = rtrans(d, c, ui, vi, wi, s1, s2);
        let t = d.lam_fv(hi_fv, lt_ty, pr);
        d.lam_fv(i_fv, nat, t)
    };
    let ty = {
        let concl = eq_on(d, p, n, u, w);
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h1_ty, t);
        let t = d.pi_fv(w_fv, vec, t);
        let t = d.pi_fv(v_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(h2_fv, h2_ty, body);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(w_fv, vec, t);
        let t = d.lam_fv(v_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.eq_on_trans, ty, value)
}

// ===========================================================================
// The vector-space operations.
// ===========================================================================

/// `RN.zero : Vec := fun _ => CReal.zero`.
fn declare_zero(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let value = zero_fn(d, c);
    let ty = vec_ty(d, p);
    definition(d, p.zero, ty, value, H_OPS)
}

/// `RN.add : Vec -> Vec -> Vec`.
fn declare_add(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ui = d.apply(u, &[i]);
    let vi = d.apply(v, &[i]);
    let body = radd(d, c, ui, vi);
    let value = {
        let t = d.lam_fv(i_fv, nat, body);
        let t = d.lam_fv(v_fv, vec, t);
        d.lam_fv(u_fv, vec, t)
    };
    let ty = {
        let t = d.arrow(vec, vec);
        d.arrow(vec, t)
    };
    definition(d, p.add, ty, value, H_OPS)
}

/// `RN.neg : Vec -> Vec`.
fn declare_neg(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ui = d.apply(u, &[i]);
    let body = rneg(d, c, ui);
    let value = {
        let t = d.lam_fv(i_fv, nat, body);
        d.lam_fv(u_fv, vec, t)
    };
    let ty = d.arrow(vec, vec);
    definition(d, p.neg, ty, value, H_OPS)
}

/// `RN.sub : Vec -> Vec -> Vec := fun u v i => CReal.add (u i) (CReal.neg (v i))`.
fn declare_sub(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ui = d.apply(u, &[i]);
    let vi = d.apply(v, &[i]);
    let nvi = rneg(d, c, vi);
    let body = radd(d, c, ui, nvi);
    let value = {
        let t = d.lam_fv(i_fv, nat, body);
        let t = d.lam_fv(v_fv, vec, t);
        d.lam_fv(u_fv, vec, t)
    };
    let ty = {
        let t = d.arrow(vec, vec);
        d.arrow(vec, t)
    };
    definition(d, p.sub, ty, value, H_OPS)
}

/// `RN.smul : CReal -> Vec -> Vec`.
fn declare_smul(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ui = d.apply(u, &[i]);
    let body = rmul(d, c, a, ui);
    let value = {
        let t = d.lam_fv(i_fv, nat, body);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let t = d.arrow(vec, vec);
        d.arrow(carrier, t)
    };
    definition(d, p.smul, ty, value, H_OPS)
}

/// The pointwise `CReal` congruence a [`declare_binary_congr`] step supplies:
/// given `u i`, `u' i`, `v i`, `v' i` and the two coordinate equivalences, a
/// proof that the operation's values agree.
type PointwiseCongr<'a> =
    &'a dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId;

/// `RN.add_congr` / `RN.sub_congr` share this shape: four vectors, two `EqOn`
/// hypotheses, a pointwise `CReal` congruence under the binder.
fn declare_binary_congr(
    d: &mut IntDev<'_>,
    p: RNPrelude,
    name: NameId,
    op: NameId,
    pointwise: PointwiseCongr<'_>,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let up_fv = d.fresh_fvar();
    let up = d.kernel().fvar(up_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let vp_fv = d.fresh_fvar();
    let vp = d.kernel().fvar(vp_fv);
    let h1_ty = eq_on(d, p, n, u, up);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = eq_on(d, p, n, v, vp);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let body = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let ui = d.apply(u, &[i]);
        let upi = d.apply(up, &[i]);
        let vi = d.apply(v, &[i]);
        let vpi = d.apply(vp, &[i]);
        let s1 = d.apply(h1, &[i, hi]);
        let s2 = d.apply(h2, &[i, hi]);
        let pr = pointwise(d, ui, upi, vi, vpi, s1, s2);
        let t = d.lam_fv(hi_fv, lt_ty, pr);
        d.lam_fv(i_fv, nat, t)
    };
    let ty = {
        let lhs = d.const_app(op, &[u, v]);
        let rhs = d.const_app(op, &[up, vp]);
        let concl = eq_on(d, p, n, lhs, rhs);
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h1_ty, t);
        let t = d.pi_fv(vp_fv, vec, t);
        let t = d.pi_fv(v_fv, vec, t);
        let t = d.pi_fv(up_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(h2_fv, h2_ty, body);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(vp_fv, vec, t);
        let t = d.lam_fv(v_fv, vec, t);
        let t = d.lam_fv(up_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, name, ty, value)
}

/// `RN.add_congr`.
fn declare_add_congr(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    declare_binary_congr(d, p, p.add_congr, p.add, &|d, a, ap, b, bp, h1, h2| {
        d.lemma(c.add_congr, &[a, ap, b, bp, h1, h2])
    })
}

/// `RN.sub_congr`.
fn declare_sub_congr(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    declare_binary_congr(d, p, p.sub_congr, p.sub, &|d, a, ap, b, bp, h1, h2| {
        let nb = rneg(d, c, b);
        let nbp = rneg(d, c, bp);
        let hn = d.lemma(c.neg_congr, &[b, bp, h2]);
        d.lemma(c.add_congr, &[a, ap, nb, nbp, h1, hn])
    })
}

/// `RN.smul_congr : forall n a a' u u', Equiv a a' -> EqOn n u u' ->
/// EqOn n (smul a u) (smul a' u')`.
fn declare_smul_congr(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let carrier = rty(d, c);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let ap_fv = d.fresh_fvar();
    let ap = d.kernel().fvar(ap_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let up_fv = d.fresh_fvar();
    let up = d.kernel().fvar(up_fv);
    let ha_ty = req(d, c, a, ap);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let hu_ty = eq_on(d, p, n, u, up);
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let body = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let ui = d.apply(u, &[i]);
        let upi = d.apply(up, &[i]);
        let step = d.apply(hu, &[i, hi]);
        let pr = d.lemma(c.mul_congr, &[a, ap, ui, upi, ha, step]);
        let t = d.lam_fv(hi_fv, lt_ty, pr);
        d.lam_fv(i_fv, nat, t)
    };
    let ty = {
        let lhs = d.const_app(p.smul, &[a, u]);
        let rhs = d.const_app(p.smul, &[ap, up]);
        let concl = eq_on(d, p, n, lhs, rhs);
        let t = d.arrow(hu_ty, concl);
        let t = d.arrow(ha_ty, t);
        let t = d.pi_fv(up_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        let t = d.pi_fv(ap_fv, carrier, t);
        let t = d.pi_fv(a_fv, carrier, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(hu_fv, hu_ty, body);
        let t = d.lam_fv(ha_fv, ha_ty, t);
        let t = d.lam_fv(up_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        let t = d.lam_fv(ap_fv, carrier, t);
        let t = d.lam_fv(a_fv, carrier, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.smul_congr, ty, value)
}

/// The four abelian-group laws, each stated up to `EqOn n` and each proved by
/// the corresponding `CReal` law under the index binder. They are what makes
/// "ℝⁿ is a real vector space" a statement about the SETOID rather than about
/// representatives.
fn declare_group_laws(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);

    // add_comm
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let body = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_ty = nat_lt(d, i, n);
            let hi_fv = d.fresh_fvar();
            let ui = d.apply(u, &[i]);
            let vi = d.apply(v, &[i]);
            let pr = d.lemma(c.add_comm, &[ui, vi]);
            let t = d.lam_fv(hi_fv, lt_ty, pr);
            d.lam_fv(i_fv, nat, t)
        };
        let lhs = vadd(d, p, u, v);
        let rhs = vadd(d, p, v, u);
        let ty = {
            let concl = eq_on(d, p, n, lhs, rhs);
            let t = d.pi_fv(v_fv, vec, concl);
            let t = d.pi_fv(u_fv, vec, t);
            d.pi_fv(n_fv, nat, t)
        };
        let value = {
            let t = d.lam_fv(v_fv, vec, body);
            let t = d.lam_fv(u_fv, vec, t);
            d.lam_fv(n_fv, nat, t)
        };
        theorem(d, p.add_comm, ty, value)?;
    }

    // add_assoc
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let body = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_ty = nat_lt(d, i, n);
            let hi_fv = d.fresh_fvar();
            let ui = d.apply(u, &[i]);
            let vi = d.apply(v, &[i]);
            let wi = d.apply(w, &[i]);
            let pr = d.lemma(c.add_assoc, &[ui, vi, wi]);
            let t = d.lam_fv(hi_fv, lt_ty, pr);
            d.lam_fv(i_fv, nat, t)
        };
        let uv = vadd(d, p, u, v);
        let lhs = vadd(d, p, uv, w);
        let vw = vadd(d, p, v, w);
        let rhs = vadd(d, p, u, vw);
        let ty = {
            let concl = eq_on(d, p, n, lhs, rhs);
            let t = d.pi_fv(w_fv, vec, concl);
            let t = d.pi_fv(v_fv, vec, t);
            let t = d.pi_fv(u_fv, vec, t);
            d.pi_fv(n_fv, nat, t)
        };
        let value = {
            let t = d.lam_fv(w_fv, vec, body);
            let t = d.lam_fv(v_fv, vec, t);
            let t = d.lam_fv(u_fv, vec, t);
            d.lam_fv(n_fv, nat, t)
        };
        theorem(d, p.add_assoc, ty, value)?;
    }

    // add_zero
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let body = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_ty = nat_lt(d, i, n);
            let hi_fv = d.fresh_fvar();
            let ui = d.apply(u, &[i]);
            let pr = d.lemma(c.add_zero, &[ui]);
            let t = d.lam_fv(hi_fv, lt_ty, pr);
            d.lam_fv(i_fv, nat, t)
        };
        let zv = d.kernel().const_(p.zero, vec![]);
        let lhs = vadd(d, p, u, zv);
        let ty = {
            let concl = eq_on(d, p, n, lhs, u);
            let t = d.pi_fv(u_fv, vec, concl);
            d.pi_fv(n_fv, nat, t)
        };
        let value = {
            let t = d.lam_fv(u_fv, vec, body);
            d.lam_fv(n_fv, nat, t)
        };
        theorem(d, p.add_zero, ty, value)?;
    }

    // add_neg
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let body = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_ty = nat_lt(d, i, n);
            let hi_fv = d.fresh_fvar();
            let ui = d.apply(u, &[i]);
            let pr = d.lemma(c.add_neg, &[ui]);
            let t = d.lam_fv(hi_fv, lt_ty, pr);
            d.lam_fv(i_fv, nat, t)
        };
        let nu = d.const_app(p.neg, &[u]);
        let lhs = vadd(d, p, u, nu);
        let zv = d.kernel().const_(p.zero, vec![]);
        let ty = {
            let concl = eq_on(d, p, n, lhs, zv);
            let t = d.pi_fv(u_fv, vec, concl);
            d.pi_fv(n_fv, nat, t)
        };
        let value = {
            let t = d.lam_fv(u_fv, vec, body);
            d.lam_fv(n_fv, nat, t)
        };
        theorem(d, p.add_neg, ty, value)?;
    }

    Ok(())
}

// ===========================================================================
// The inner product.
// ===========================================================================

/// The summand `fun i => CReal.mul (u i) (v i)`.
fn dot_summand(d: &mut IntDev<'_>, c: CRealPrelude, u: ExprId, v: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ui = d.apply(u, &[i]);
    let vi = d.apply(v, &[i]);
    let body = rmul(d, c, ui, vi);
    d.lam_fv(i_fv, nat, body)
}

/// `RN.dot : Vec -> Vec -> Nat -> CReal`.
fn declare_dot(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let carrier = rty(d, c);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let f = dot_summand(d, c, u, v);
    let body = rsum(d, c, f, n);
    let value = {
        let t = d.lam_fv(n_fv, nat, body);
        let t = d.lam_fv(v_fv, vec, t);
        d.lam_fv(u_fv, vec, t)
    };
    let ty = {
        let t = d.arrow(nat, carrier);
        let t = d.arrow(vec, t);
        d.arrow(vec, t)
    };
    definition(d, p.dot, ty, value, H_DOT)
}

/// `RN.dot_zero : forall u v, Equiv (dot u v Nat.zero) CReal.zero`.
fn declare_dot_zero(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let zn = d.zero();
    let z = rzero(d, c);
    let lhs = dot(d, p, u, v, zn);
    let body = rrefl(d, c, z);
    let ty = {
        let concl = req(d, c, lhs, z);
        let t = d.pi_fv(v_fv, vec, concl);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(v_fv, vec, body);
        d.lam_fv(u_fv, vec, t)
    };
    theorem(d, p.dot_zero, ty, value)
}

/// `RN.dot_succ : forall u v n,
/// Equiv (dot u v (succ n)) (add (dot u v n) (mul (u n) (v n)))`.
fn declare_dot_succ(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sn = d.succ(n);
    let lhs = dot(d, p, u, v, sn);
    let prior = dot(d, p, u, v, n);
    let un = d.apply(u, &[n]);
    let vn = d.apply(v, &[n]);
    let last = rmul(d, c, un, vn);
    let rhs = radd(d, c, prior, last);
    let body = rrefl(d, c, rhs);
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(n_fv, nat, concl);
        let t = d.pi_fv(v_fv, vec, t);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, body);
        let t = d.lam_fv(v_fv, vec, t);
        d.lam_fv(u_fv, vec, t)
    };
    theorem(d, p.dot_succ, ty, value)
}

/// `RN.dot_comm : forall u v n, Equiv (dot u v n) (dot v u n)`.
fn declare_dot_comm(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let f = dot_summand(d, c, u, v);
    let g = dot_summand(d, c, v, u);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let pr = d.lemma(c.mul_comm, &[ui, vi]);
        d.lam_fv(i_fv, nat, pr)
    };
    let body = d.lemma(c.sum_range_congr, &[f, g, n, pointwise]);

    let lhs = dot(d, p, u, v, n);
    let rhs = dot(d, p, v, u, n);
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(n_fv, nat, concl);
        let t = d.pi_fv(v_fv, vec, t);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, body);
        let t = d.lam_fv(v_fv, vec, t);
        d.lam_fv(u_fv, vec, t)
    };
    theorem(d, p.dot_comm, ty, value)
}

/// `RN.dot_congr : forall n u u' v v', EqOn n u u' -> EqOn n v v' ->
/// Equiv (dot u v n) (dot u' v' n)`.
fn declare_dot_congr(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let up_fv = d.fresh_fvar();
    let up = d.kernel().fvar(up_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let vp_fv = d.fresh_fvar();
    let vp = d.kernel().fvar(vp_fv);
    let h1_ty = eq_on(d, p, n, u, up);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = eq_on(d, p, n, v, vp);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let f = dot_summand(d, c, u, v);
    let g = dot_summand(d, c, up, vp);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let ui = d.apply(u, &[i]);
        let upi = d.apply(up, &[i]);
        let vi = d.apply(v, &[i]);
        let vpi = d.apply(vp, &[i]);
        let s1 = d.apply(h1, &[i, hi]);
        let s2 = d.apply(h2, &[i, hi]);
        let pr = d.lemma(c.mul_congr, &[ui, upi, vi, vpi, s1, s2]);
        let t = d.lam_fv(hi_fv, lt_ty, pr);
        d.lam_fv(i_fv, nat, t)
    };
    let body = d.lemma(p.creal_sum_range_congr_lt, &[f, g, n, pointwise]);

    let lhs = dot(d, p, u, v, n);
    let rhs = dot(d, p, up, vp, n);
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h1_ty, t);
        let t = d.pi_fv(vp_fv, vec, t);
        let t = d.pi_fv(v_fv, vec, t);
        let t = d.pi_fv(up_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(h2_fv, h2_ty, body);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(vp_fv, vec, t);
        let t = d.lam_fv(v_fv, vec, t);
        let t = d.lam_fv(up_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.dot_congr, ty, value)
}

/// `RN.dot_add_left : forall a b v n,
/// Equiv (dot (add a b) v n) (add (dot a v n) (dot b v n))`.
fn declare_dot_add_left(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let ab = vadd(d, p, a, b);
    let f_lhs = dot_summand(d, c, ab, v);
    let f_a = dot_summand(d, c, a, v);
    let f_b = dot_summand(d, c, b, v);
    // fun i => add (a i * v i) (b i * v i)
    let f_split = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ai = d.apply(a, &[i]);
        let bi = d.apply(b, &[i]);
        let vi = d.apply(v, &[i]);
        let m1 = rmul(d, c, ai, vi);
        let m2 = rmul(d, c, bi, vi);
        let body = radd(d, c, m1, m2);
        d.lam_fv(i_fv, nat, body)
    };
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ai = d.apply(a, &[i]);
        let bi = d.apply(b, &[i]);
        let vi = d.apply(v, &[i]);
        let pr = d.lemma(p.creal_right_distrib, &[ai, bi, vi]);
        d.lam_fv(i_fv, nat, pr)
    };
    let s_lhs = rsum(d, c, f_lhs, n);
    let s_split = rsum(d, c, f_split, n);
    let step1 = d.lemma(c.sum_range_congr, &[f_lhs, f_split, n, pointwise]);
    let step2 = d.lemma(c.sum_range_add, &[f_a, f_b, n]);
    let s_a = rsum(d, c, f_a, n);
    let s_b = rsum(d, c, f_b, n);
    let rhs = radd(d, c, s_a, s_b);
    let (_, body) = rchain(d, c, s_lhs, &[(s_split, step1), (rhs, step2)]);

    let lhs_t = dot(d, p, ab, v, n);
    let ra = dot(d, p, a, v, n);
    let rb = dot(d, p, b, v, n);
    let rhs_t = radd(d, c, ra, rb);
    let ty = {
        let concl = req(d, c, lhs_t, rhs_t);
        let t = d.pi_fv(n_fv, nat, concl);
        let t = d.pi_fv(v_fv, vec, t);
        let t = d.pi_fv(b_fv, vec, t);
        d.pi_fv(a_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, body);
        let t = d.lam_fv(v_fv, vec, t);
        let t = d.lam_fv(b_fv, vec, t);
        d.lam_fv(a_fv, vec, t)
    };
    theorem(d, p.dot_add_left, ty, value)
}

/// `RN.dot_add_right : forall u a b n,
/// Equiv (dot u (add a b) n) (add (dot u a n) (dot u b n))` — `dot_comm` on the
/// outside and on each summand, around `dot_add_left`.
fn declare_dot_add_right(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let ab = vadd(d, p, a, b);
    let lhs = dot(d, p, u, ab, n);
    let swapped = dot(d, p, ab, u, n);
    let da = dot(d, p, a, u, n);
    let db = dot(d, p, b, u, n);
    let split = radd(d, c, da, db);
    let ua = dot(d, p, u, a, n);
    let ub = dot(d, p, u, b, n);
    let rhs = radd(d, c, ua, ub);

    let s1 = d.lemma(p.dot_comm, &[u, ab, n]);
    let s2 = d.lemma(p.dot_add_left, &[a, b, u, n]);
    let ca = d.lemma(p.dot_comm, &[a, u, n]);
    let cb = d.lemma(p.dot_comm, &[b, u, n]);
    let s3 = d.lemma(c.add_congr, &[da, ua, db, ub, ca, cb]);
    let (_, body) = rchain(d, c, lhs, &[(swapped, s1), (split, s2), (rhs, s3)]);

    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(n_fv, nat, concl);
        let t = d.pi_fv(b_fv, vec, t);
        let t = d.pi_fv(a_fv, vec, t);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, body);
        let t = d.lam_fv(b_fv, vec, t);
        let t = d.lam_fv(a_fv, vec, t);
        d.lam_fv(u_fv, vec, t)
    };
    theorem(d, p.dot_add_right, ty, value)
}

/// `RN.dot_smul_left : forall w u v n,
/// Equiv (dot (smul w u) v n) (mul w (dot u v n))`.
fn declare_dot_smul_left(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let carrier = rty(d, c);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let wu = d.const_app(p.smul, &[w, u]);
    let f_lhs = dot_summand(d, c, wu, v);
    let f_uv = dot_summand(d, c, u, v);
    // fun i => mul w (mul (u i) (v i))
    let f_pull = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let inner = rmul(d, c, ui, vi);
        let body = rmul(d, c, w, inner);
        d.lam_fv(i_fv, nat, body)
    };
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let pr = d.lemma(c.mul_assoc, &[w, ui, vi]);
        d.lam_fv(i_fv, nat, pr)
    };
    let s_lhs = rsum(d, c, f_lhs, n);
    let s_pull = rsum(d, c, f_pull, n);
    let s_uv = rsum(d, c, f_uv, n);
    let target = rmul(d, c, w, s_uv);
    let step1 = d.lemma(c.sum_range_congr, &[f_lhs, f_pull, n, pointwise]);
    let fwd = d.lemma(c.mul_sum_range, &[w, f_uv, n]);
    let step2 = rsymm(d, c, target, s_pull, fwd);
    let (_, body) = rchain(d, c, s_lhs, &[(s_pull, step1), (target, step2)]);

    let lhs_t = dot(d, p, wu, v, n);
    let inner_t = dot(d, p, u, v, n);
    let rhs_t = rmul(d, c, w, inner_t);
    let ty = {
        let concl = req(d, c, lhs_t, rhs_t);
        let t = d.pi_fv(n_fv, nat, concl);
        let t = d.pi_fv(v_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(w_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, body);
        let t = d.lam_fv(v_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(w_fv, carrier, t)
    };
    theorem(d, p.dot_smul_left, ty, value)
}

/// `RN.dot_self_nonneg : forall u n, le zero (dot u u n)`.
fn declare_dot_self_nonneg(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let z = rzero(d, c);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let s = dot(d, p, u, u, x);
        rle(d, c, z, s)
    };
    let stmt = motive(d, n);
    let proof = d.induct(
        &motive,
        &|d| d.lemma(c.le_refl, &[z]),
        &|d, j, ih| {
            let prior = dot(d, p, u, u, j);
            let uj = d.apply(u, &[j]);
            let sq = rmul(d, c, uj, uj);
            let hsq = d.lemma(c.sq_nonneg, &[uj]);
            d.lemma(p.creal_add_nonneg, &[prior, sq, ih, hsq])
        },
        n,
    );

    let ty = {
        let t = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(u_fv, vec, t)
    };
    theorem(d, p.dot_self_nonneg, ty, value)
}

/// `RN.dot_two : forall u v,
/// Equiv (dot u v 2) (add (mul (u 0) (v 0)) (mul (u 1) (v 1)))`.
fn declare_dot_two(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let n0 = d.num(0);
    let n1 = d.num(1);
    let n2 = d.num(2);
    let z = rzero(d, c);
    let u0 = d.apply(u, &[n0]);
    let v0 = d.apply(v, &[n0]);
    let u1 = d.apply(u, &[n1]);
    let v1 = d.apply(v, &[n1]);
    let m0 = rmul(d, c, u0, v0);
    let m1 = rmul(d, c, u1, v1);
    let zm0 = radd(d, c, z, m0);
    let rhs = radd(d, c, m0, m1);

    let za = d.lemma(p.creal_zero_add, &[m0]); // Equiv (0 + m0) m0
    let refl_m1 = rrefl(d, c, m1);
    let body = d.lemma(c.add_congr, &[zm0, m0, m1, m1, za, refl_m1]);

    let lhs_t = dot(d, p, u, v, n2);
    let ty = {
        let concl = req(d, c, lhs_t, rhs);
        let t = d.pi_fv(v_fv, vec, concl);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(v_fv, vec, body);
        d.lam_fv(u_fv, vec, t)
    };
    theorem(d, p.dot_two, ty, value)
}

// ===========================================================================
// The norm, and Cauchy-Schwarz.
// ===========================================================================

/// `RN.norm : Vec -> Nat -> CReal := fun u n => CReal.sqrt (dot u u n)`.
fn declare_norm(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let carrier = rty(d, c);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let dd = dot(d, p, u, u, n);
    let body = rsqrt(d, c, dd);
    let value = {
        let t = d.lam_fv(n_fv, nat, body);
        d.lam_fv(u_fv, vec, t)
    };
    let ty = {
        let t = d.arrow(nat, carrier);
        d.arrow(vec, t)
    };
    definition(d, p.norm, ty, value, H_NORM)
}

/// `RN.norm_nonneg : forall u n, le zero (norm u n)`.
fn declare_norm_nonneg(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let z = rzero(d, c);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let dd = dot(d, p, u, u, n);
    let body = d.lemma(c.sqrt_nonneg, &[dd]);
    let nrm = norm(d, p, u, n);
    let ty = {
        let concl = rle(d, c, z, nrm);
        let t = d.pi_fv(n_fv, nat, concl);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, body);
        d.lam_fv(u_fv, vec, t)
    };
    theorem(d, p.norm_nonneg, ty, value)
}

/// `RN.norm_sq : forall u n, Equiv (mul (norm u n) (norm u n)) (dot u u n)`.
fn declare_norm_sq(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let dd = dot(d, p, u, u, n);
    let nonneg = d.lemma(p.dot_self_nonneg, &[u, n]);
    let body = d.lemma(c.mul_self_sqrt, &[dd, nonneg]);

    let nrm = norm(d, p, u, n);
    let sq = rmul(d, c, nrm, nrm);
    let ty = {
        let concl = req(d, c, sq, dd);
        let t = d.pi_fv(n_fv, nat, concl);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, body);
        d.lam_fv(u_fv, vec, t)
    };
    theorem(d, p.norm_sq, ty, value)
}

/// `RN.norm_congr : forall n u u', EqOn n u u' -> Equiv (norm u n) (norm u' n)`.
fn declare_norm_congr(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let up_fv = d.fresh_fvar();
    let up = d.kernel().fvar(up_fv);
    let h_ty = eq_on(d, p, n, u, up);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let du = dot(d, p, u, u, n);
    let dup = dot(d, p, up, up, n);
    let inner = d.lemma(p.dot_congr, &[n, u, up, u, up, h, h]);
    let body = d.lemma(c.sqrt_congr, &[du, dup, inner]);

    let nu = norm(d, p, u, n);
    let nup = norm(d, p, up, n);
    let ty = {
        let concl = req(d, c, nu, nup);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(up_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(up_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.norm_congr, ty, value)
}

/// `RN.cauchy_schwarz : forall u v n, le (dot u v n) (mul (norm u n) (norm v n))`.
///
/// **Unsquared Cauchy-Schwarz at symbolic dimension**, and the theorem this
/// module exists to make possible. Induction on the bound; the step is where
/// the argument is, and the argument is a GENERALIZATION of
/// `Metric.CPoint.dotLeSqrtMul` rather than a rebuild of it.
///
/// Write `A := <u,u>ₙ`, `C := <v,v>ₙ`, `x := uₙ`, `y := vₙ`. At `n+1` the
/// target is
///
/// ```text
/// <u,v>ₙ + x·y  ≤  sqrt(A + x²) · sqrt(C + y²)
/// ```
///
/// The induction hypothesis bounds the first summand by `sqrt A · sqrt C`, so
/// it suffices that
///
/// ```text
/// sqrt A · sqrt C + x·y  ≤  sqrt((A + x²)(C + y²))
/// ```
///
/// and **that is exactly `dotLeSqrtMul` at the two PLANE points**
/// `P := (sqrt A, x)` and `Q := (sqrt C, y)`: its left-hand side `CPoint.dot P Q`
/// is definitionally `sqrt A · sqrt C + x·y`, and `CPoint.dot P P` is
/// `sqrt A · sqrt A + x·x`, which `CReal.mul_self_sqrt` (available because
/// `A ≥ 0` by [`RNPrelude::dot_self_nonneg`]) rewrites to `A + x²`. One
/// `CReal.sqrt_mul` splits the root at the end. So the n-dimensional inequality
/// is the 2-dimensional one applied `n` times, with the norm carrying the
/// accumulated dimensions in its first coordinate.
///
/// The base case is `0 ≤ sqrt 0 · sqrt 0`, closed by `mul_self_sqrt` at zero.
///
/// Note what does NOT appear: no discriminant, no minimizing scalar, no case
/// split on whether `<u,u>` vanishes. `Rat.dotN_cauchy_schwarz` needs all
/// three because ℚ's proof runs through `t := -(B/A)` and so must separate
/// `A = 0` from `A > 0`; over `CReal` that case split is not even available
/// (there is no `le_total`), which is exactly why the plane lemma had to be
/// the engine.
fn declare_cauchy_schwarz(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let cp = p.metric.cpoint;
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = dot(d, p, u, v, x);
        let nu = norm(d, p, u, x);
        let nv = norm(d, p, v, x);
        let rhs = rmul(d, c, nu, nv);
        rle(d, c, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            // `dot u v 0` is `zero`, `norm u 0` is `sqrt zero`.
            let z = rzero(d, c);
            let sq = rsqrt(d, c, z);
            let prod = rmul(d, c, sq, sq);
            let refl_z = rrefl(d, c, z);
            let le_z = d.lemma(c.le_refl, &[z]);
            let z_nonneg = d.lemma(c.le_refl, &[z]);
            let fwd = d.lemma(c.mul_self_sqrt, &[z, z_nonneg]); // Equiv (sqrt 0 · sqrt 0) 0
            let bwd = rsymm(d, c, prod, z, fwd);
            d.lemma(c.le_congr, &[z, z, z, prod, refl_z, bwd, le_z])
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let a_j = dot(d, p, u, u, j);
            let c_j = dot(d, p, v, v, j);
            let b_j = dot(d, p, u, v, j);
            let sa = rsqrt(d, c, a_j); // = norm u j
            let sc = rsqrt(d, c, c_j); // = norm v j
            let x = d.apply(u, &[j]);
            let y = d.apply(v, &[j]);
            let xy = rmul(d, c, x, y);
            let xx = rmul(d, c, x, x);
            let yy = rmul(d, c, y, y);
            let a_n = radd(d, c, a_j, xx); // = dot u u (succ j)
            let c_n = radd(d, c, c_j, yy);
            let sa_n = rsqrt(d, c, a_n); // = norm u (succ j)
            let sc_n = rsqrt(d, c, c_n);
            let target = rmul(d, c, sa_n, sc_n);

            // (a) the induction hypothesis, plus the untouched last term.
            let plane_lhs = {
                let m = rmul(d, c, sa, sc);
                radd(d, c, m, xy)
            };
            let start = radd(d, c, b_j, xy);
            let ih_prod = rmul(d, c, sa, sc);
            let refl_xy = d.lemma(c.le_refl, &[xy]);
            let s1 = d.lemma(c.add_le_add, &[b_j, ih_prod, xy, xy, ih, refl_xy]);

            // (b) the plane lemma at P := (sqrt A, x), Q := (sqrt C, y).
            let pp = d.const_app(cp.mk, &[sa, x]);
            let qq = d.const_app(cp.mk, &[sc, y]);
            let cs = d.lemma(p.metric.cpoint_dot_le_sqrt_mul, &[pp, qq]);

            // (c) `CPoint.dot P P` is `sqrt A · sqrt A + x·x`; rewrite to `A + x·x`.
            let sasa = rmul(d, c, sa, sa);
            let scsc = rmul(d, c, sc, sc);
            let pp_dot = radd(d, c, sasa, xx);
            let qq_dot = radd(d, c, scsc, yy);
            let a_nonneg = d.lemma(p.dot_self_nonneg, &[u, j]);
            let c_nonneg = d.lemma(p.dot_self_nonneg, &[v, j]);
            let ea_inner = d.lemma(c.mul_self_sqrt, &[a_j, a_nonneg]);
            let ec_inner = d.lemma(c.mul_self_sqrt, &[c_j, c_nonneg]);
            let refl_xx = rrefl(d, c, xx);
            let refl_yy = rrefl(d, c, yy);
            let ea = d.lemma(c.add_congr, &[sasa, a_j, xx, xx, ea_inner, refl_xx]);
            let ec = d.lemma(c.add_congr, &[scsc, c_j, yy, yy, ec_inner, refl_yy]);
            let prod_old = rmul(d, c, pp_dot, qq_dot);
            let prod_new = rmul(d, c, a_n, c_n);
            let em = d.lemma(c.mul_congr, &[pp_dot, a_n, qq_dot, c_n, ea, ec]);
            let root_old = rsqrt(d, c, prod_old);
            let root_new = rsqrt(d, c, prod_new);
            let es = d.lemma(c.sqrt_congr, &[prod_old, prod_new, em]);
            let an_nonneg = d.lemma(p.dot_self_nonneg, &[u, sj]);
            let cn_nonneg = d.lemma(p.dot_self_nonneg, &[v, sj]);
            let esm = d.lemma(c.sqrt_mul, &[a_n, c_n, an_nonneg, cn_nonneg]);
            let (_, e_all) = rchain(d, c, root_old, &[(root_new, es), (target, esm)]);

            // (d) transport `cs` across that equivalence, then compose.
            let refl_plane = rrefl(d, c, plane_lhs);
            let s2 = d.lemma(
                c.le_congr,
                &[
                    plane_lhs, plane_lhs, root_old, target, refl_plane, e_all, cs,
                ],
            );
            d.lemma(c.le_trans, &[start, plane_lhs, target, s1, s2])
        },
        n,
    );

    let ty = {
        let t = d.pi_fv(n_fv, nat, stmt);
        let t = d.pi_fv(v_fv, vec, t);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, proof);
        let t = d.lam_fv(v_fv, vec, t);
        d.lam_fv(u_fv, vec, t)
    };
    theorem(d, p.cauchy_schwarz, ty, value)
}

/// `RN.norm_add_le : forall u v n,
/// le (norm (add u v) n) (add (norm u n) (norm v n))` — Minkowski.
///
/// `CReal.le_of_sq_le` reduces it to `‖u+v‖² ≤ (‖u‖+‖v‖)²`; both sides expand
/// by bilinearity and `norm_sq`, and the two cross terms are bounded by
/// [`RNPrelude::cauchy_schwarz`] (once at `(u,v)` and once at `(v,u)`).
fn declare_norm_add_le(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let w = vadd(d, p, u, v);
    let t = norm(d, p, w, n); // ‖u+v‖
    let a = norm(d, p, u, n);
    let b = norm(d, p, v, n);
    let s = radd(d, c, a, b);

    let t_nonneg = d.lemma(p.norm_nonneg, &[w, n]);
    let a_nonneg = d.lemma(p.norm_nonneg, &[u, n]);
    let b_nonneg = d.lemma(p.norm_nonneg, &[v, n]);
    let s_nonneg = d.lemma(p.creal_add_nonneg, &[a, b, a_nonneg, b_nonneg]);

    // LHS: t·t ~ <u+v,u+v> ~ (<u,u> + <u,v>) + (<v,u> + <v,v>)
    let tt = rmul(d, c, t, t);
    let dww = dot(d, p, w, w, n);
    let e_tt = d.lemma(p.norm_sq, &[w, n]); // Equiv (t·t) <w,w>

    let duw = dot(d, p, u, w, n);
    let dvw = dot(d, p, v, w, n);
    let split_outer = radd(d, c, duw, dvw);
    let e1 = d.lemma(p.dot_add_left, &[u, v, w, n]);

    let duu = dot(d, p, u, u, n);
    let duv = dot(d, p, u, v, n);
    let dvu = dot(d, p, v, u, n);
    let dvv = dot(d, p, v, v, n);
    let left_pair = radd(d, c, duu, duv);
    let right_pair = radd(d, c, dvu, dvv);
    let e2a = d.lemma(p.dot_add_right, &[u, u, v, n]);
    let e2b = d.lemma(p.dot_add_right, &[v, u, v, n]);
    let e2 = d.lemma(c.add_congr, &[duw, left_pair, dvw, right_pair, e2a, e2b]);
    let expanded = radd(d, c, left_pair, right_pair);
    let (_, e_lhs) = rchain(d, c, tt, &[(dww, e_tt), (split_outer, e1), (expanded, e2)]);

    // RHS: s·s ~ (a·a + a·b) + (b·a + b·b)
    let ss = rmul(d, c, s, s);
    let sa = rmul(d, c, s, a);
    let sb = rmul(d, c, s, b);
    let split_s = radd(d, c, sa, sb);
    let r1 = d.lemma(c.left_distrib, &[s, a, b]);
    let aa = rmul(d, c, a, a);
    let ba = rmul(d, c, b, a);
    let ab = rmul(d, c, a, b);
    let bb = rmul(d, c, b, b);
    let sa_pair = radd(d, c, aa, ba);
    let sb_pair = radd(d, c, ab, bb);
    let r2a = d.lemma(p.creal_right_distrib, &[a, b, a]);
    let r2b = d.lemma(p.creal_right_distrib, &[a, b, b]);
    let r2 = d.lemma(c.add_congr, &[sa, sa_pair, sb, sb_pair, r2a, r2b]);
    let rhs_expanded = radd(d, c, sa_pair, sb_pair);
    let (_, e_rhs) = rchain(d, c, ss, &[(split_s, r1), (rhs_expanded, r2)]);

    // termwise: <u,u> ~ a·a, <u,v> ≤ a·b, <v,u> ≤ b·a, <v,v> ~ b·b
    let e_uu = d.lemma(p.norm_sq, &[u, n]); // Equiv (a·a) <u,u>
    let le_uu = {
        let back = rsymm(d, c, aa, duu, e_uu); // Equiv <u,u> (a·a)
        d.lemma(c.le_of_equiv, &[duu, aa, back])
    };
    let e_vv = d.lemma(p.norm_sq, &[v, n]);
    let le_vv = {
        let back = rsymm(d, c, bb, dvv, e_vv);
        d.lemma(c.le_of_equiv, &[dvv, bb, back])
    };
    let le_uv = d.lemma(p.cauchy_schwarz, &[u, v, n]); // <u,v> ≤ a·b
    let le_vu = d.lemma(p.cauchy_schwarz, &[v, u, n]); // <v,u> ≤ b·a
    let left_le = d.lemma(c.add_le_add, &[duu, aa, duv, ab, le_uu, le_uv]);
    let right_le = d.lemma(c.add_le_add, &[dvu, ba, dvv, bb, le_vu, le_vv]);
    // (<u,u> + <u,v>) + (<v,u> + <v,v>) ≤ (a·a + a·b) + (b·a + b·b)
    let left_target = radd(d, c, aa, ab);
    let right_target = radd(d, c, ba, bb);
    let core = d.lemma(
        c.add_le_add,
        &[
            left_pair,
            left_target,
            right_pair,
            right_target,
            left_le,
            right_le,
        ],
    );
    let core_rhs = radd(d, c, left_target, right_target);

    // Reassociate the right-hand side into `rhs_expanded`'s shape:
    // (a·a + a·b) + (b·a + b·b)  vs  (a·a + b·a) + (a·b + b·b).
    let reassoc = {
        // both are `add4` of the same four terms; go through add_assoc/add_comm.
        // (aa + ab) + (ba + bb) ~ aa + (ab + (ba + bb))
        let step1 = d.lemma(c.add_assoc, &[aa, ab, right_target]);
        let inner1 = radd(d, c, ab, right_target);
        let mid1 = radd(d, c, aa, inner1);
        // ab + (ba + bb) ~ (ab + ba) + bb
        let ab_ba = radd(d, c, ab, ba);
        let ab_ba_bb = radd(d, c, ab_ba, bb);
        let fwd_inner = d.lemma(c.add_assoc, &[ab, ba, bb]);
        let step2_inner = rsymm(d, c, ab_ba_bb, inner1, fwd_inner);
        // ab + ba ~ ba + ab
        let ba_ab = radd(d, c, ba, ab);
        let comm = d.lemma(c.add_comm, &[ab, ba]);
        let refl_bb = rrefl(d, c, bb);
        let step3_inner = d.lemma(c.add_congr, &[ab_ba, ba_ab, bb, bb, comm, refl_bb]);
        let ba_ab_bb = radd(d, c, ba_ab, bb);
        // (ba + ab) + bb ~ ba + (ab + bb)
        let ab_bb = radd(d, c, ab, bb);
        let step4_inner = d.lemma(c.add_assoc, &[ba, ab, bb]);
        let ba_rest = radd(d, c, ba, ab_bb);
        let (_, inner_chain) = rchain(
            d,
            c,
            inner1,
            &[
                (ab_ba_bb, step2_inner),
                (ba_ab_bb, step3_inner),
                (ba_rest, step4_inner),
            ],
        );
        let refl_aa = rrefl(d, c, aa);
        let step5 = d.lemma(
            c.add_congr,
            &[aa, aa, inner1, ba_rest, refl_aa, inner_chain],
        );
        let mid2 = radd(d, c, aa, ba_rest);
        // aa + (ba + (ab + bb)) ~ (aa + ba) + (ab + bb)
        let fwd_outer = d.lemma(c.add_assoc, &[aa, ba, ab_bb]);
        let step6 = rsymm(d, c, rhs_expanded, mid2, fwd_outer);
        let (_, pr) = rchain(
            d,
            c,
            core_rhs,
            &[(mid1, step1), (mid2, step5), (rhs_expanded, step6)],
        );
        pr
    };

    // Assemble: t·t ~ expanded ≤ core_rhs ~ rhs_expanded ~ s·s
    let e_rhs_back = rsymm(d, c, ss, rhs_expanded, e_rhs);
    let (_, right_chain) = rchain(d, c, core_rhs, &[(rhs_expanded, reassoc), (ss, e_rhs_back)]);
    let e_lhs_back = rsymm(d, c, tt, expanded, e_lhs);
    let sq_le = d.lemma(
        c.le_congr,
        &[expanded, tt, core_rhs, ss, e_lhs_back, right_chain, core],
    );
    let body = d.lemma(c.le_of_sq_le, &[t, s, t_nonneg, s_nonneg, sq_le]);

    let ty = {
        let concl = rle(d, c, t, s);
        let t0 = d.pi_fv(n_fv, nat, concl);
        let t0 = d.pi_fv(v_fv, vec, t0);
        d.pi_fv(u_fv, vec, t0)
    };
    let value = {
        let t0 = d.lam_fv(n_fv, nat, body);
        let t0 = d.lam_fv(v_fv, vec, t0);
        d.lam_fv(u_fv, vec, t0)
    };
    theorem(d, p.norm_add_le, ty, value)
}

// ===========================================================================
// The metric instance.
// ===========================================================================

/// `RN.dist : Nat -> Vec -> Vec -> CReal := fun n u v => norm (sub u v) n`.
///
/// The dimension comes FIRST here (unlike `dot`/`norm`) so that the `Metric`
/// record's `dist : carrier -> carrier -> CReal` field is the partial
/// application `RN.dist n`, with no eta-expanding lambda in the instance.
fn declare_dist(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let carrier = rty(d, c);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let w = vsub(d, p, u, v);
    let body = norm(d, p, w, n);
    let value = {
        let t = d.lam_fv(v_fv, vec, body);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    let ty = {
        let t = d.arrow(vec, carrier);
        let t = d.arrow(vec, t);
        d.arrow(nat, t)
    };
    definition(d, p.dist, ty, value, H_DIST)
}

/// `RN.dist_congr`.
fn declare_dist_congr(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let up_fv = d.fresh_fvar();
    let up = d.kernel().fvar(up_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let vp_fv = d.fresh_fvar();
    let vp = d.kernel().fvar(vp_fv);
    let h1_ty = eq_on(d, p, n, u, up);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = eq_on(d, p, n, v, vp);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let w = vsub(d, p, u, v);
    let wp = vsub(d, p, up, vp);
    let hw = d.lemma(p.sub_congr, &[n, u, up, v, vp, h1, h2]);
    let body = d.lemma(p.norm_congr, &[n, w, wp, hw]);

    let lhs = vdist(d, p, n, u, v);
    let rhs = vdist(d, p, n, up, vp);
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h1_ty, t);
        let t = d.pi_fv(vp_fv, vec, t);
        let t = d.pi_fv(v_fv, vec, t);
        let t = d.pi_fv(up_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(h2_fv, h2_ty, body);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(vp_fv, vec, t);
        let t = d.lam_fv(v_fv, vec, t);
        let t = d.lam_fv(up_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.dist_congr, ty, value)
}

/// `RN.dist_nonneg : forall n u v, le zero (dist n u v)`.
fn declare_dist_nonneg(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let z = rzero(d, c);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let w = vsub(d, p, u, v);
    let body = d.lemma(p.norm_nonneg, &[w, n]);
    let dst = vdist(d, p, n, u, v);
    let ty = {
        let concl = rle(d, c, z, dst);
        let t = d.pi_fv(v_fv, vec, concl);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(v_fv, vec, body);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.dist_nonneg, ty, value)
}

/// `RN.dist_self : forall n u v, EqOn n u v -> Equiv (dist n u v) zero`.
fn declare_dist_self(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let z = rzero(d, c);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let h_ty = eq_on(d, p, n, u, v);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let w = vsub(d, p, u, v);
    let f = dot_summand(d, c, w, w);
    let g = zero_fn(d, c);
    // Every summand below `n` vanishes.
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let nvi = rneg(d, c, vi);
        let wi = radd(d, c, ui, nvi);
        let step = d.apply(h, &[i, hi]); // Equiv (u i) (v i)
        let refl_nvi = rrefl(d, c, nvi);
        let to_vv = d.lemma(c.add_congr, &[ui, vi, nvi, nvi, step, refl_nvi]);
        let vnv = radd(d, c, vi, nvi);
        let vnv_zero = d.lemma(c.add_neg, &[vi]);
        let (_, wi_zero) = rchain(d, c, wi, &[(vnv, to_vv), (z, vnv_zero)]);
        let sq = rmul(d, c, wi, wi);
        let zz = rmul(d, c, z, z);
        let sq_zz = d.lemma(c.mul_congr, &[wi, z, wi, z, wi_zero, wi_zero]);
        let zz_z = d.lemma(c.mul_zero, &[z]);
        let (_, pr) = rchain(d, c, sq, &[(zz, sq_zz), (z, zz_z)]);
        let t = d.lam_fv(hi_fv, lt_ty, pr);
        d.lam_fv(i_fv, nat, t)
    };
    let sum_f = rsum(d, c, f, n);
    let sum_g = rsum(d, c, g, n);
    let e1 = d.lemma(p.creal_sum_range_congr_lt, &[f, g, n, pointwise]);
    let e2 = d.lemma(p.creal_sum_range_zero_const, &[n]);
    let (_, sum_zero) = rchain(d, c, sum_f, &[(sum_g, e1), (z, e2)]);
    let root_sum = rsqrt(d, c, sum_f);
    let root_zero = rsqrt(d, c, z);
    let e3 = d.lemma(c.sqrt_congr, &[sum_f, z, sum_zero]);
    let e4 = d.kernel().const_(c.sqrt_zero, vec![]);
    let (_, body) = rchain(d, c, root_sum, &[(root_zero, e3), (z, e4)]);

    let dst = vdist(d, p, n, u, v);
    let ty = {
        let concl = req(d, c, dst, z);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(v_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(v_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.dist_self, ty, value)
}

/// `RN.dist_eqOn : forall n u v, Equiv (dist n u v) zero -> EqOn n u v`.
///
/// The record's `distEquiv` field, and the direction with the content:
/// `sqrt <w,w> ~ 0` gives `<w,w> ~ 0` (square both sides through
/// `mul_self_sqrt`), then [`RNPrelude::creal_sum_range_term_zero`] pushes the
/// vanishing down to every summand below `n`,
/// `CReal.eq_zero_of_mul_self_zero` strips the square, and
/// [`RNPrelude::creal_eq_of_sub_zero`] turns `uᵢ - vᵢ ~ 0` into `uᵢ ~ vᵢ`.
fn declare_dist_eq_on(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let z = rzero(d, c);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let w = vsub(d, p, u, v);
    let dst = vdist(d, p, n, u, v);
    let h_ty = req(d, c, dst, z);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let dww = dot(d, p, w, w, n);
    let nonneg = d.lemma(p.dot_self_nonneg, &[w, n]);
    let root = rsqrt(d, c, dww);
    let sq = rmul(d, c, root, root);
    let sq_eq = d.lemma(c.mul_self_sqrt, &[dww, nonneg]); // Equiv (root·root) <w,w>
    let back = rsymm(d, c, sq, dww, sq_eq); // Equiv <w,w> (root·root)
    let zz = rmul(d, c, z, z);
    let to_zz = d.lemma(c.mul_congr, &[root, z, root, z, h, h]);
    let zz_z = d.lemma(c.mul_zero, &[z]);
    let (_, dww_zero) = rchain(d, c, dww, &[(sq, back), (zz, to_zz), (z, zz_z)]);

    let f = dot_summand(d, c, w, w);
    let f_nonneg = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let uj = d.apply(u, &[j]);
        let vj = d.apply(v, &[j]);
        let nvj = rneg(d, c, vj);
        let wj = radd(d, c, uj, nvj);
        let pr = d.lemma(c.sq_nonneg, &[wj]);
        d.lam_fv(j_fv, nat, pr)
    };
    let terms = d.lemma(p.creal_sum_range_term_zero, &[f, n, f_nonneg, dww_zero]);

    let body = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let nvi = rneg(d, c, vi);
        let wi = radd(d, c, ui, nvi);
        let term_zero = d.apply(terms, &[i, hi]); // Equiv (wi·wi) zero
        let wi_zero = d.lemma(c.eq_zero_of_mul_self_zero, &[wi, term_zero]);
        let pr = d.lemma(p.creal_eq_of_sub_zero, &[ui, vi, wi_zero]);
        let t = d.lam_fv(hi_fv, lt_ty, pr);
        d.lam_fv(i_fv, nat, t)
    };

    let ty = {
        let concl = eq_on(d, p, n, u, v);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(v_fv, vec, t);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(v_fv, vec, t);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.dist_eq_on, ty, value)
}

/// `RN.dist_comm : forall n u v, Equiv (dist n u v) (dist n v u)`.
fn declare_dist_comm(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let w = vsub(d, p, u, v);
    let wr = vsub(d, p, v, u);
    let f = dot_summand(d, c, w, w);
    let g = dot_summand(d, c, wr, wr);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let nui = rneg(d, c, ui);
        let nvi = rneg(d, c, vi);
        let wi = radd(d, c, ui, nvi);
        let wri = radd(d, c, vi, nui);
        let nwi = rneg(d, c, wi);
        let neg_sub = d.lemma(p.creal_neg_sub, &[ui, vi]); // Equiv wri (neg wi)
        let sq_wi = rmul(d, c, wi, wi);
        let sq_wri = rmul(d, c, wri, wri);
        let sq_nwi = rmul(d, c, nwi, nwi);
        let to_neg = d.lemma(c.mul_congr, &[wri, nwi, wri, nwi, neg_sub, neg_sub]);
        let neg_sq = d.lemma(c.neg_mul_neg, &[wi]); // Equiv (nwi·nwi) (wi·wi)
        let (_, pr) = rchain(d, c, sq_wri, &[(sq_nwi, to_neg), (sq_wi, neg_sq)]);
        d.lam_fv(i_fv, nat, pr)
    };
    let sum_g = rsum(d, c, g, n);
    let sum_f = rsum(d, c, f, n);
    let inner = d.lemma(c.sum_range_congr, &[g, f, n, pointwise]);
    let root_inner = d.lemma(c.sqrt_congr, &[sum_g, sum_f, inner]);
    let root_g = rsqrt(d, c, sum_g);
    let root_f = rsqrt(d, c, sum_f);
    let body = rsymm(d, c, root_g, root_f, root_inner);

    let lhs = vdist(d, p, n, u, v);
    let rhs = vdist(d, p, n, v, u);
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(v_fv, vec, concl);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(v_fv, vec, body);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.dist_comm, ty, value)
}

/// `RN.dist_triangle : forall n a b e,
/// le (dist n a e) (add (dist n a b) (dist n b e))`.
///
/// `sub a e` and `add (sub a b) (sub b e)` agree at EVERY index (not merely
/// below `n`) by `Metric.CReal.subTelescope`, so `norm_congr` moves the
/// left-hand side onto Minkowski's shape and [`RNPrelude::norm_add_le`] closes.
fn declare_dist_triangle(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let ae = vsub(d, p, a, e);
    let ab = vsub(d, p, a, b);
    let be = vsub(d, p, b, e);
    let sum = vadd(d, p, ab, be);

    let telescope = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = nat_lt(d, i, n);
        let hi_fv = d.fresh_fvar();
        let ai = d.apply(a, &[i]);
        let bi = d.apply(b, &[i]);
        let ei = d.apply(e, &[i]);
        let fwd = d.lemma(p.metric.creal_sub_telescope, &[ai, bi, ei]);
        // `fwd : Equiv ((a-b) + (b-c)) (a-c)`; the field needs the other way.
        let nbi = rneg(d, c, bi);
        let nei = rneg(d, c, ei);
        let abi = radd(d, c, ai, nbi);
        let bei = radd(d, c, bi, nei);
        let sumi = radd(d, c, abi, bei);
        let aei = radd(d, c, ai, nei);
        let pr = rsymm(d, c, sumi, aei, fwd);
        let t = d.lam_fv(hi_fv, lt_ty, pr);
        d.lam_fv(i_fv, nat, t)
    };

    let n_ae = norm(d, p, ae, n);
    let n_sum = norm(d, p, sum, n);
    let shift = d.lemma(p.norm_congr, &[n, ae, sum, telescope]);
    let mink = d.lemma(p.norm_add_le, &[ab, be, n]);
    let n_ab = norm(d, p, ab, n);
    let n_be = norm(d, p, be, n);
    let bound = radd(d, c, n_ab, n_be);
    let back = rsymm(d, c, n_ae, n_sum, shift);
    let refl_bound = rrefl(d, c, bound);
    let body = d.lemma(
        c.le_congr,
        &[n_sum, n_ae, bound, bound, back, refl_bound, mink],
    );

    let lhs = vdist(d, p, n, a, e);
    let d1 = vdist(d, p, n, a, b);
    let d2 = vdist(d, p, n, b, e);
    let rhs = radd(d, c, d1, d2);
    let ty = {
        let concl = rle(d, c, lhs, rhs);
        let t = d.pi_fv(e_fv, vec, concl);
        let t = d.pi_fv(b_fv, vec, t);
        let t = d.pi_fv(a_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(e_fv, vec, body);
        let t = d.lam_fv(b_fv, vec, t);
        let t = d.lam_fv(a_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.dist_triangle, ty, value)
}

/// `RN.metric : Nat -> Metric` — the instance, one metric space per dimension.
fn declare_metric_instance(
    d: &mut IntDev<'_>,
    _c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let equiv = d.const_app(p.eq_on, &[n]);
    let equiv_refl = d.const_app(p.eq_on_refl, &[n]);
    let equiv_symm = d.const_app(p.eq_on_symm, &[n]);
    let equiv_trans = d.const_app(p.eq_on_trans, &[n]);
    let dist = d.const_app(p.dist, &[n]);
    let dist_congr = d.const_app(p.dist_congr, &[n]);
    let dist_nonneg = d.const_app(p.dist_nonneg, &[n]);
    let dist_self = d.const_app(p.dist_self, &[n]);
    let dist_equiv = d.const_app(p.dist_eq_on, &[n]);
    let dist_comm = d.const_app(p.dist_comm, &[n]);
    let dist_triangle = d.const_app(p.dist_triangle, &[n]);

    let args = [
        vec,
        equiv,
        equiv_refl,
        equiv_symm,
        equiv_trans,
        dist,
        dist_congr,
        dist_nonneg,
        dist_self,
        dist_equiv,
        dist_comm,
        dist_triangle,
    ];
    let body = mk_instance(d.kernel(), &p.metric.record, &args);
    let value = d.lam_fv(n_fv, nat, body);
    let metric_ty = d.kernel().const_(p.metric.record.ind, vec![]);
    let ty = d.arrow(nat, metric_ty);
    definition(d, p.metric_inst, ty, value, H_INST)
}

/// `RN.metric_dist : forall n u v,
/// Equiv (Metric.dist (RN.metric n) u v) (RN.dist n u v)` — by `Equiv.refl`.
fn declare_metric_dist(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let inst = d.const_app(p.metric_inst, &[n]);
    let selector = d
        .kernel()
        .const_(p.metric.record.sel(crate::METRIC_DIST), vec![]);
    let lhs = d.apply(selector, &[inst, u, v]);
    let rhs = vdist(d, p, n, u, v);
    let body = rrefl(d, c, rhs);

    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(v_fv, vec, concl);
        let t = d.pi_fv(u_fv, vec, t);
        d.pi_fv(n_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(v_fv, vec, body);
        let t = d.lam_fv(u_fv, vec, t);
        d.lam_fv(n_fv, nat, t)
    };
    theorem(d, p.metric_dist, ty, value)
}

// ===========================================================================
// The bridge to the plane.
// ===========================================================================

/// `RN.ofCPoint : CPoint -> Vec`.
fn declare_of_cpoint(d: &mut IntDev<'_>, c: CRealPrelude, p: RNPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let vec = vec_ty(d, p);
    let cp = p.metric.cpoint;
    let point = d.kernel().const_(cp.point, vec![]);
    let carrier = rty(d, c);

    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let px = d.const_app(cp.x, &[pt]);
    let py = d.const_app(cp.y, &[pt]);

    let anon = d.anon_name();
    let motive = d
        .kernel()
        .lam(anon, nat, carrier, crate::BinderInfo::Default);
    let step = {
        let k_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let inner = d.lam_fv(ih_fv, carrier, py);
        d.lam_fv(k_fv, nat, inner)
    };
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let l1 = {
        let l0 = d.kernel().level_zero();
        d.kernel().level_succ(l0)
    };
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![l1]);
    let applied = d.apply(rec, &[motive, px, step, i]);
    let body = d.lam_fv(i_fv, nat, applied);
    let value = d.lam_fv(pt_fv, point, body);
    let ty = d.arrow(point, vec);
    definition(d, p.of_cpoint, ty, value, H_OPS)
}

/// `RN.ofCPoint_dot : forall P Q,
/// Equiv (dot (ofCPoint P) (ofCPoint Q) 2) (CPoint.dot P Q)`.
fn declare_of_cpoint_dot(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let cp = p.metric.cpoint;
    let point = d.kernel().const_(cp.point, vec![]);
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let qt_fv = d.fresh_fvar();
    let qt = d.kernel().fvar(qt_fv);

    let z = rzero(d, c);
    let px = d.const_app(cp.x, &[pt]);
    let py = d.const_app(cp.y, &[pt]);
    let qx = d.const_app(cp.x, &[qt]);
    let qy = d.const_app(cp.y, &[qt]);
    let m0 = rmul(d, c, px, qx);
    let m1 = rmul(d, c, py, qy);
    let zm0 = radd(d, c, z, m0);
    let za = d.lemma(p.creal_zero_add, &[m0]);
    let refl_m1 = rrefl(d, c, m1);
    let body = d.lemma(c.add_congr, &[zm0, m0, m1, m1, za, refl_m1]);

    let n2 = d.num(2);
    let vp = d.const_app(p.of_cpoint, &[pt]);
    let vq = d.const_app(p.of_cpoint, &[qt]);
    let lhs = dot(d, p, vp, vq, n2);
    let rhs = d.const_app(cp.dot, &[pt, qt]);
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(qt_fv, point, concl);
        d.pi_fv(pt_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(qt_fv, point, body);
        d.lam_fv(pt_fv, point, t)
    };
    theorem(d, p.of_cpoint_dot, ty, value)
}

/// `RN.ofCPoint_distSq : forall P Q,
/// Equiv (dot (sub (ofCPoint P) (ofCPoint Q)) (sub (ofCPoint P) (ofCPoint Q)) 2)
/// (CPoint.distSq P Q)`.
fn declare_of_cpoint_dist_sq(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let cp = p.metric.cpoint;
    let point = d.kernel().const_(cp.point, vec![]);
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let qt_fv = d.fresh_fvar();
    let qt = d.kernel().fvar(qt_fv);

    let z = rzero(d, c);
    let px = d.const_app(cp.x, &[pt]);
    let py = d.const_app(cp.y, &[pt]);
    let qx = d.const_app(cp.x, &[qt]);
    let qy = d.const_app(cp.y, &[qt]);
    let nqx = rneg(d, c, qx);
    let nqy = rneg(d, c, qy);
    let dx = radd(d, c, px, nqx);
    let dy = radd(d, c, py, nqy);
    let m0 = rmul(d, c, dx, dx);
    let m1 = rmul(d, c, dy, dy);
    let zm0 = radd(d, c, z, m0);
    let za = d.lemma(p.creal_zero_add, &[m0]);
    let refl_m1 = rrefl(d, c, m1);
    let body = d.lemma(c.add_congr, &[zm0, m0, m1, m1, za, refl_m1]);

    let n2 = d.num(2);
    let vp = d.const_app(p.of_cpoint, &[pt]);
    let vq = d.const_app(p.of_cpoint, &[qt]);
    let w = vsub(d, p, vp, vq);
    let lhs = dot(d, p, w, w, n2);
    let rhs = d.const_app(cp.dist_sq, &[pt, qt]);
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(qt_fv, point, concl);
        d.pi_fv(pt_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(qt_fv, point, body);
        d.lam_fv(pt_fv, point, t)
    };
    theorem(d, p.of_cpoint_dist_sq, ty, value)
}

/// `RN.ofCPoint_dist : forall P Q,
/// Equiv (RN.dist 2 (ofCPoint P) (ofCPoint Q)) (Metric.CPoint.dist P Q)`.
fn declare_of_cpoint_dist(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let cp = p.metric.cpoint;
    let point = d.kernel().const_(cp.point, vec![]);
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let qt_fv = d.fresh_fvar();
    let qt = d.kernel().fvar(qt_fv);

    let n2 = d.num(2);
    let vp = d.const_app(p.of_cpoint, &[pt]);
    let vq = d.const_app(p.of_cpoint, &[qt]);
    let w = vsub(d, p, vp, vq);
    let inner_lhs = dot(d, p, w, w, n2);
    let inner_rhs = d.const_app(cp.dist_sq, &[pt, qt]);
    let agree = d.lemma(p.of_cpoint_dist_sq, &[pt, qt]);
    let body = d.lemma(c.sqrt_congr, &[inner_lhs, inner_rhs, agree]);

    let lhs = vdist(d, p, n2, vp, vq);
    let rhs = d.const_app(p.metric.cpoint_dist, &[pt, qt]);
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(qt_fv, point, concl);
        d.pi_fv(pt_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(qt_fv, point, body);
        d.lam_fv(pt_fv, point, t)
    };
    theorem(d, p.of_cpoint_dist, ty, value)
}

/// `RN.ofCPoint_congr : forall P Q, CPoint.Equiv P Q -> EqOn 2 (ofCPoint P) (ofCPoint Q)`.
///
/// The index binder has to be case-split (`ofCPoint P i` is a stuck `Nat.rec`
/// at a variable `i`), so the proof is `Nat.rec` on `i` with the `Nat.lt i 2`
/// hypothesis simply discarded in both branches: index `0` is the `x`
/// coordinate, every successor is the `y` coordinate, and the two halves of
/// `CPoint.Equiv` supply exactly those.
fn declare_of_cpoint_congr(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let cp = p.metric.cpoint;
    let point = d.kernel().const_(cp.point, vec![]);
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let qt_fv = d.fresh_fvar();
    let qt = d.kernel().fvar(qt_fv);
    let h_ty = d.const_app(cp.point_equiv, &[pt, qt]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let px = d.const_app(cp.x, &[pt]);
    let py = d.const_app(cp.y, &[pt]);
    let qx = d.const_app(cp.x, &[qt]);
    let qy = d.const_app(cp.y, &[qt]);
    let left_ty = req(d, c, px, qx);
    let right_ty = req(d, c, py, qy);
    let hx = d.and_left(left_ty, right_ty, h);
    let hy = d.and_right(left_ty, right_ty, h);

    let vp = d.const_app(p.of_cpoint, &[pt]);
    let vq = d.const_app(p.of_cpoint, &[qt]);
    let n2 = d.num(2);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lt_ty = nat_lt(d, x, n2);
        let a = d.apply(vp, &[x]);
        let b = d.apply(vq, &[x]);
        let eqv = req(d, c, a, b);
        d.arrow(lt_ty, eqv)
    };
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let proof = d.induct(
        &motive,
        &|d| {
            let zn = d.zero();
            let lt_ty = nat_lt(d, zn, n2);
            let hi_fv = d.fresh_fvar();
            d.lam_fv(hi_fv, lt_ty, hx)
        },
        &|d, j, _ih| {
            let sj = d.succ(j);
            let lt_ty = nat_lt(d, sj, n2);
            let hi_fv = d.fresh_fvar();
            d.lam_fv(hi_fv, lt_ty, hy)
        },
        i,
    );
    let body = d.lam_fv(i_fv, nat, proof);

    let ty = {
        let concl = eq_on(d, p, n2, vp, vq);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(qt_fv, point, t);
        d.pi_fv(pt_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(qt_fv, point, t);
        d.lam_fv(pt_fv, point, t)
    };
    theorem(d, p.of_cpoint_congr, ty, value)
}

/// `RN.cpointEquiv_of_eqOn : forall P Q,
/// EqOn 2 (ofCPoint P) (ofCPoint Q) -> CPoint.Equiv P Q`.
fn declare_cpoint_equiv_of_eq_on(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: RNPrelude,
) -> Result<(), KernelError> {
    let cp = p.metric.cpoint;
    let point = d.kernel().const_(cp.point, vec![]);
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let qt_fv = d.fresh_fvar();
    let qt = d.kernel().fvar(qt_fv);

    let vp = d.const_app(p.of_cpoint, &[pt]);
    let vq = d.const_app(p.of_cpoint, &[qt]);
    let n2 = d.num(2);
    let h_ty = eq_on(d, p, n2, vp, vq);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let n0 = d.num(0);
    let n1 = d.num(1);
    let zero_lt = d.prelude().zero_lt_succ;
    let lt_succ_self = d.prelude().lt_succ_self;
    let h0_arg = d.const_app(zero_lt, &[n1]); // Nat.lt 0 (succ 1)
    let h1_arg = d.const_app(lt_succ_self, &[n1]); // Nat.lt 1 (succ 1)
    let s0 = d.apply(h, &[n0, h0_arg]);
    let s1 = d.apply(h, &[n1, h1_arg]);

    let px = d.const_app(cp.x, &[pt]);
    let py = d.const_app(cp.y, &[pt]);
    let qx = d.const_app(cp.x, &[qt]);
    let qy = d.const_app(cp.y, &[qt]);
    let left_ty = req(d, c, px, qx);
    let right_ty = req(d, c, py, qy);
    let intro = c.rat.int.logic.and_intro;
    let body = d.const_app(intro, &[left_ty, right_ty, s0, s1]);

    let concl = d.const_app(cp.point_equiv, &[pt, qt]);
    let ty = {
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(qt_fv, point, t);
        d.pi_fv(pt_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(qt_fv, point, t);
        d.lam_fv(pt_fv, point, t)
    };
    theorem(d, p.cpoint_equiv_of_eq_on, ty, value)
}

#[cfg(test)]
mod rn_tests;
