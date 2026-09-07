//! `Metric.completion` — **the carrier of the metric completion**, and the
//! measurement that decided its shape (ADR-1678).
//!
//! Lane `metric-completion`. A NEW top-level module, not a submodule of
//! `metric.rs`, for the same three reasons `metric_prod.rs` is one: everything
//! here is built from `MetricPrelude`'s **public** surface, `metric.rs`'s own
//! build pipeline is untouched so the `Metric` prelude's cost does not move,
//! and no file another lane owns is edited.
//!
//! ## What ADR-1678 measured, in one paragraph
//!
//! [ADR-1625] specified this construction over a carrier
//! `Subtype (Nat → M.carrier) (Metric.Regular M)` and priced it at "four new
//! lemmas about `CReal.limit`". **`Metric.Regular` does not exist** — every
//! `Regular` token in the metric tree is `ReducibilityHint::Regular(1)` — and
//! it does not need to, because [`MetricPrelude::cauchy_at`] at the modulus
//! `1` unfolds to exactly Bishop's regularity condition
//! `d(f m, f n) ≤ 1/(m+1) + 1/(n+1)`. The four lemmas are off the critical
//! path too: `CReal.limit` is the term former this development abandoned (it
//! has no consumers anywhere in the crate), and the live route
//! `CReal.mk (speedup (diagonal D) K) (regular_of_scaled_cauchy …)` already
//! has all three of its bridges shipped, the last of which **names** the
//! limit — so the completion's `dist` sits inside `CReal`'s ordinary
//! `Converges` algebra rather than needing a new one. See ADR-1678 for the
//! counts and the method behind them.
//!
//! ## The modulus is fixed at `1`, and that is forced
//!
//! [`MetricPrelude::cauchy`] is `∃ K, Metric.CauchyAt M f K` — a `Prop`.
//! `Exists.rec` is `Prop`-only, so a carrier built on it can never hand `K`
//! back to a `dist` field that must produce a `CReal`. This is the same kernel
//! fact `CReal.scaledCauchy_of_abs_diff_le` exists to work around, stated in
//! its own doc comment ("`regular_of_scaled_cauchy` needs the `(K, per-pair)`
//! pair as DATA, and `Exists.rec` is `Prop`-only"). Fixing the modulus at `1`
//! rather than carrying it as a `Sigma` component is the cheaper of the two
//! data-carrying options: any `CauchyAt M f K` sequence is `RegularSeq` after
//! a reindex, and carrying `K` would put a modulus-combination step in every
//! one of the twelve field witnesses.
//!
//! **This is the lane's first mutant, and the kernel decides it** — see
//! `metric_completion/metric_completion_tests.rs`.
//!
//! ## What is declared here
//!
//! | name | type |
//! | --- | --- |
//! | `Metric.RegularSeq` | `Π (M : Metric), (Nat → M.carrier) → Prop` |
//! | `Metric.regularSeq_cauchyAt` | `∀ M f, Eq Prop (RegularSeq M f) (CauchyAt M f 1)` |
//! | `Metric.regularSeq_bound` | `∀ M f, RegularSeq M f → ∀ m n, le (M.dist (f m) (f n)) (ofRat (1/(m+1) + 1/(n+1)))` |
//! | `Metric.CompletionSeq` | `Metric → Sort 1` |
//! | `Metric.completionSeq_carrier` | `∀ M, Eq (Sort 1) (CompletionSeq M) (Subtype (Nat → M.carrier) (RegularSeq M))` |
//! | `Metric.completionVal` | `Π M, CompletionSeq M → Nat → M.carrier` |
//! | `Metric.completionRegular` | `∀ M x, RegularSeq M (completionVal M x)` |
//! | `Metric.completionDistSeq` | `Π M, CompletionSeq M → CompletionSeq M → Nat → CReal` |
//! | `Metric.completionDistSeq_eval` | `∀ M x y n, Eq CReal (completionDistSeq M x y n) (M.dist (completionVal M x n) (completionVal M y n))` |
//! | `Metric.embedSeq` | `Π M, M.carrier → CompletionSeq M` |
//! | `Metric.embedSeq_val` | `∀ M a n, Eq M.carrier (completionVal M (embedSeq M a) n) a` |
//! | `Metric.embedSeq_dist` | `∀ M a b n, Eq CReal (completionDistSeq M (embedSeq M a) (embedSeq M b) n) (M.dist a b)` |
//! | `Metric.embedSeq_reflects` | `∀ M a b, (∀ n, CReal.Equiv (completionDistSeq M (embedSeq M a) (embedSeq M b) n) CReal.zero) → M.equiv a b` |
//!
//! `Metric.regularSeq_bound` is the discriminating one. `regularSeq_cauchyAt`
//! is an alias equation and would still hold if the modulus were wrong;
//! `regularSeq_bound` spells the rate out — `Rat.natDivSucc 1 m` on the nose —
//! so changing the modulus breaks it. **A reduction probe between two names is
//! not an evaluation test; the one that writes the value out is.**
//!
//! `Metric.embedSeq_dist` is the **isometry**, at the level this slice can
//! express it: the distance SEQUENCE between two embedded points is constant
//! at `M.dist a b`, so whatever limit the completion's `dist` takes of it is
//! `M.dist a b` on the nose. It is an `Eq` and not a `CReal.le` deliberately —
//! a merely NON-EXPANDING map satisfies the `le` form, and
//! `Metric.embedSeq_reflects` is the consequence that separates them, because
//! an upper bound of zero on the image distance says nothing about the source.
//!
//! ## What is NOT here, and the exact obstruction
//!
//! `Metric.completionDist` (the `CReal.mk`-built distance), the `Metric`
//! instance itself, and completeness. The single blocking step is
//! **`Metric.dist_diff_le`**, the four-point reverse triangle inequality
//!
//! ```text
//! ∀ M a b c e, CReal.le (CReal.abs (CReal.add (M.dist a b) (CReal.neg (M.dist c e))))
//!                       (CReal.add (M.dist a c) (M.dist b e))
//! ```
//!
//! which is what `CReal.scaledCauchy_of_abs_diff_le` consumes.
//! `Metric.dist_quadrilateral M a c e b` already gives
//! `d a b ≤ d a c + (d c e + d e b)`; turning that into
//! `d a b + (-(d c e)) ≤ d a c + d b e` needs `CReal`'s
//! `(A + (C + B)) + (-C) ~ A + B` rearrangement, which is
//! `add_assoc`/`add_comm`/`add_neg`/`add_zero` and is **not** a named lemma in
//! `creal.rs`. That rearrangement is the whole gap; nothing after it is new
//! (ADR-1678).
//!
//! [ADR-1625]: ../../../docs/research/09-decisions/adr-1625-l1-is-a-metric-space-from-a-pointwise-distance-and-the-completion-functor-does-not-exist-yet.md

// `MetricPrelude` is a 15 kB `Copy` handle carrying the whole `CRealPrelude`;
// passing it by value trips `large_types_passed_by_value` on every helper, the
// same suppression and the same reason as `metric.rs` and `metric_prod.rs`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names
)]

use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::MetricPrelude;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rle, rzero};

#[cfg(test)]
mod metric_completion_tests;

/// The selector indices this file reads. Kept as named constants rather than
/// bare integers for the same reason `metric.rs` does it.
const CARRIER: usize = 0;
const EQUIV: usize = 1;
const DIST: usize = 5;
const DIST_EQUIV: usize = 9;

/// The interned names this file owns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MetricCompletionNames {
    /// `Metric.RegularSeq : Π (M : Metric), (Nat → M.carrier) → Prop
    /// := fun M f => Metric.CauchyAt M f 1` — Bishop regularity, which this
    /// library already had under another name (ADR-1678 measurement 1).
    pub regular_seq: NameId,
    /// `Metric.regularSeq_cauchyAt : ∀ M f,
    /// Eq Prop (Metric.RegularSeq M f) (Metric.CauchyAt M f 1)` — `Eq.refl`.
    /// The alias equation; NOT the evaluation test.
    pub regular_seq_cauchy_at: NameId,
    /// `Metric.regularSeq_bound : ∀ M f, Metric.RegularSeq M f → ∀ m n,
    /// CReal.le (M.dist (f m) (f n))
    ///          (CReal.ofRat (Rat.add (Rat.natDivSucc 1 m)
    ///                                (Rat.natDivSucc 1 n)))`.
    ///
    /// **The evaluation test**: it writes the modulus out, so a `RegularSeq`
    /// stated at any other rate fails to admit it.
    pub regular_seq_bound: NameId,
    /// `Metric.CompletionSeq : Metric → Sort 1
    /// := fun M => Subtype (Nat → M.carrier) (Metric.RegularSeq M)`.
    pub completion_seq: NameId,
    /// `Metric.completionSeq_carrier : ∀ M, Eq (Sort 1) (CompletionSeq M)
    /// (Subtype (Nat → M.carrier) (Metric.RegularSeq M))` — `Eq.refl`.
    pub completion_seq_carrier: NameId,
    /// `Metric.completionVal : Π (M : Metric), CompletionSeq M → Nat →
    /// M.carrier` — the underlying sequence.
    pub completion_val: NameId,
    /// `Metric.completionRegular : ∀ M x,
    /// Metric.RegularSeq M (Metric.completionVal M x)` — `Subtype.property`.
    pub completion_regular: NameId,
    /// `Metric.completionDistSeq : Π (M : Metric), CompletionSeq M →
    /// CompletionSeq M → Nat → CReal` — the `Nat → CReal` sequence whose limit
    /// is the completion's distance. **This is the object ADR-1625's reuse
    /// count was wrong about**: it is a sequence of REALS, so every
    /// `CReal.converges_*` theorem instantiates at it.
    pub completion_dist_seq: NameId,
    /// `Metric.completionDistSeq_eval : ∀ M x y n, Eq CReal
    /// (completionDistSeq M x y n)
    /// (M.dist (completionVal M x n) (completionVal M y n))` — `Eq.refl`.
    pub completion_dist_seq_eval: NameId,
    /// `Metric.embedSeq : Π (M : Metric), M.carrier → CompletionSeq M` — a
    /// point as the constant sequence at it. Its regularity witness is
    /// `Metric.dist_self` widened by `CReal.le_of_equiv_le`-shaped
    /// nonnegativity of the rate; see [`declare_embed_seq`].
    pub embed_seq: NameId,
    /// `Metric.embedSeq_val : ∀ M a n,
    /// Eq M.carrier (completionVal M (embedSeq M a) n) a` — `Eq.refl`: the
    /// embedding really is the constant sequence, not merely something
    /// equivalent to it.
    pub embed_seq_val: NameId,
    /// `Metric.embedSeq_dist : ∀ M a b n, Eq CReal
    /// (Metric.completionDistSeq M (embedSeq M a) (embedSeq M b) n)
    /// (M.dist a b)` — **the embedding is an isometry**, stated at the level
    /// this slice can express it (the distance SEQUENCE, before its limit).
    ///
    /// It is an `Eq` and not a `CReal.le`: a non-expanding map would satisfy
    /// the `le` form, and [`Self::embed_seq_reflects`] is the theorem that
    /// separates the two.
    pub embed_seq_dist: NameId,
    /// `Metric.embedSeq_reflects : ∀ M a b,
    /// (∀ n, CReal.Equiv (completionDistSeq M (embedSeq M a) (embedSeq M b) n)
    ///                   CReal.zero) →
    /// M.equiv a b`.
    ///
    /// **The isometry's discriminating consequence.** A non-expanding map —
    /// one with only `dist (f a) (f b) ≤ dist a b` — cannot prove this: from
    /// an upper bound of `0` on the image distance nothing follows about the
    /// source distance. `M.distEquiv` applied to `h 0`, and the whole proof is
    /// one line because `completionDistSeq M (embedSeq M a) (embedSeq M b) n`
    /// reduces definitionally to `M.dist a b`.
    pub embed_seq_reflects: NameId,
}

impl MetricCompletionNames {
    /// Every name this file owns, for the inventory tests. Derived from the
    /// struct's own fields, never a literal list somewhere else.
    ///
    /// Named `owned_names`, not `all`: `check-kernel-trusted-core.py` resolves
    /// method calls loosely by name and the trusted core calls `.all(..)` on
    /// other receivers, so `all` here would pull this content file into the
    /// trusted closure (the `MetricProdNames`/`ImageGroupNames` finding).
    pub fn owned_names(&self) -> Vec<(&'static str, NameId)> {
        vec![
            ("Metric.RegularSeq", self.regular_seq),
            ("Metric.regularSeq_cauchyAt", self.regular_seq_cauchy_at),
            ("Metric.regularSeq_bound", self.regular_seq_bound),
            ("Metric.CompletionSeq", self.completion_seq),
            ("Metric.completionSeq_carrier", self.completion_seq_carrier),
            ("Metric.completionVal", self.completion_val),
            ("Metric.completionRegular", self.completion_regular),
            ("Metric.completionDistSeq", self.completion_dist_seq),
            (
                "Metric.completionDistSeq_eval",
                self.completion_dist_seq_eval,
            ),
            ("Metric.embedSeq", self.embed_seq),
            ("Metric.embedSeq_val", self.embed_seq_val),
            ("Metric.embedSeq_dist", self.embed_seq_dist),
            ("Metric.embedSeq_reflects", self.embed_seq_reflects),
        ]
    }
}

fn intern(kernel: &mut Kernel, metric: NameId) -> MetricCompletionNames {
    MetricCompletionNames {
        regular_seq: kernel.name_str(metric, "RegularSeq"),
        regular_seq_cauchy_at: kernel.name_str(metric, "regularSeq_cauchyAt"),
        regular_seq_bound: kernel.name_str(metric, "regularSeq_bound"),
        completion_seq: kernel.name_str(metric, "CompletionSeq"),
        completion_seq_carrier: kernel.name_str(metric, "completionSeq_carrier"),
        completion_val: kernel.name_str(metric, "completionVal"),
        completion_regular: kernel.name_str(metric, "completionRegular"),
        completion_dist_seq: kernel.name_str(metric, "completionDistSeq"),
        completion_dist_seq_eval: kernel.name_str(metric, "completionDistSeq_eval"),
        embed_seq: kernel.name_str(metric, "embedSeq"),
        embed_seq_val: kernel.name_str(metric, "embedSeq_val"),
        embed_seq_dist: kernel.name_str(metric, "embedSeq_dist"),
        embed_seq_reflects: kernel.name_str(metric, "embedSeq_reflects"),
    }
}

/// The pieces almost every declaration here opens: a generic `M`, its carrier,
/// the sequence type `Nat → M.carrier`, and the two `Subtype` heads.
struct Space {
    metric_ty: ExprId,
    m_fv: u64,
    m: ExprId,
    /// `Metric.carrier M`.
    carrier: ExprId,
    /// `Nat → Metric.carrier M`.
    seq_ty: ExprId,
    /// `Metric.RegularSeq M`, ready to apply to a sequence.
    regular_head: ExprId,
    /// `Subtype.{1} (Nat → M.carrier) (Metric.RegularSeq M)`.
    sub_carrier: ExprId,
    /// `Subtype.val.{1} (Nat → M.carrier) (Metric.RegularSeq M)`.
    val_head: ExprId,
}

/// The generic space, WITHOUT the `RegularSeq`-dependent pieces — usable
/// before `Metric.RegularSeq` is declared.
fn bare_space(d: &mut IntDev<'_>, p: MetricPrelude) -> (ExprId, u64, ExprId, ExprId, ExprId) {
    let metric_ty = d.kernel().const_(p.record.ind, vec![]);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let carrier = {
        let s = d.kernel().const_(p.record.sel(CARRIER), vec![]);
        d.apply(s, &[m])
    };
    let nat = d.nat_ty();
    let seq_ty = d.arrow(nat, carrier);
    (metric_ty, m_fv, m, carrier, seq_ty)
}

fn space(d: &mut IntDev<'_>, c: CRealPrelude, p: MetricPrelude, n: MetricCompletionNames) -> Space {
    let (metric_ty, m_fv, m, carrier, seq_ty) = bare_space(d, p);
    let logic = c.rat.int.logic;
    let one = d.level_one();
    let regular_head = d.const_app(n.regular_seq, &[m]);
    let sub_carrier = {
        let head = d.kernel().const_(logic.sigma.subtype, vec![one]);
        d.apply(head, &[seq_ty, regular_head])
    };
    let val_head = {
        let head = d.kernel().const_(logic.sigma.subtype_val, vec![one]);
        d.apply(head, &[seq_ty, regular_head])
    };
    Space {
        metric_ty,
        m_fv,
        m,
        carrier,
        seq_ty,
        regular_head,
        sub_carrier,
        val_head,
    }
}

/// `M`'s field `i`, already applied to `M`.
fn field(d: &mut IntDev<'_>, p: MetricPrelude, m: ExprId, i: usize) -> ExprId {
    let s = d.kernel().const_(p.record.sel(i), vec![]);
    d.apply(s, &[m])
}

fn definition(
    d: &mut IntDev<'_>,
    name: NameId,
    ty: ExprId,
    value: ExprId,
) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

fn theorem(d: &mut IntDev<'_>, name: NameId, ty: ExprId, value: ExprId) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// The carrier predicate.
// ---------------------------------------------------------------------------

/// `Metric.RegularSeq : Π (M : Metric), (Nat → M.carrier) → Prop
///   := fun M f => Metric.CauchyAt M f 1`.
///
/// Zero new estimates: `Metric.CauchyAt M f K` is
/// `∀ m n, M.dist (f m) (f n) ≤ ofRat (K/(m+1) + K/(n+1))`, so `K := 1` is
/// Bishop's regularity condition on the nose (ADR-1678 measurement 1).
fn declare_regular_seq(
    d: &mut IntDev<'_>,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let (metric_ty, m_fv, m, _carrier, seq_ty) = bare_space(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let one = d.num(1);

    let body = d.const_app(p.cauchy_at, &[m, f, one]);
    let value = {
        let t = d.lam_fv(f_fv, seq_ty, body);
        d.lam_fv(m_fv, metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(seq_ty, prop);
        d.pi_fv(m_fv, metric_ty, t)
    };
    definition(d, n.regular_seq, ty, value)
}

/// `Metric.regularSeq_cauchyAt : ∀ M f,
/// Eq Prop (Metric.RegularSeq M f) (Metric.CauchyAt M f 1)` — `Eq.refl`.
///
/// The alias equation. It is checkable and it is NOT the evaluation test: it
/// would still hold if `Metric.CauchyAt`'s own modulus argument were wrong.
/// [`declare_regular_seq_bound`] is the one that pins the rate.
fn declare_regular_seq_cauchy_at(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let logic = c.rat.int.logic;
    let (metric_ty, m_fv, m, _carrier, seq_ty) = bare_space(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let one_nat = d.num(1);

    let prop = d.kernel().sort_zero();
    let lhs = d.const_app(n.regular_seq, &[m, f]);
    let rhs = d.const_app(p.cauchy_at, &[m, f, one_nat]);

    let level_one = d.level_one();
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![level_one]);
        d.apply(head, &[prop, lhs, rhs])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![level_one]);
        d.apply(head, &[prop, rhs])
    };
    let ty = {
        let t = d.pi_fv(f_fv, seq_ty, stmt);
        d.pi_fv(m_fv, metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(f_fv, seq_ty, proof);
        d.lam_fv(m_fv, metric_ty, t)
    };
    theorem(d, n.regular_seq_cauchy_at, ty, value)
}

/// `Metric.regularSeq_bound : ∀ M f, Metric.RegularSeq M f → ∀ m n,
/// CReal.le (M.dist (f m) (f n))
///          (CReal.ofRat (Rat.add (Rat.natDivSucc 1 m) (Rat.natDivSucc 1 n)))`
/// — `fun M f h => h`.
///
/// **The evaluation test for the predicate.** The right-hand side is written
/// out rather than named, so the declaration only admits if `RegularSeq`
/// really unfolds to the modulus-`1` rate. `Metric.CauchyAt` carries
/// `ReducibilityHint::Regular(1)`, so the kernel does the unfolding.
fn declare_regular_seq_bound(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let (metric_ty, m_fv, m, _carrier, seq_ty) = bare_space(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let nat = d.nat_ty();

    let hyp = d.const_app(n.regular_seq, &[m, f]);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let dist = field(d, p, m, DIST);
    let fi = d.apply(f, &[i]);
    let fj = d.apply(f, &[j]);
    let lhs = d.apply(dist, &[fi, fj]);

    let one_nat = d.num(1);
    let rate = {
        let qi = d.const_app(c.rat.nat_div_succ, &[one_nat, i]);
        let qj = d.const_app(c.rat.nat_div_succ, &[one_nat, j]);
        let rat_add = d.int().rat_add;
        let q = d.const_app(rat_add, &[qi, qj]);
        d.const_app(c.of_rat, &[q])
    };
    let claim = d.const_app(c.le, &[lhs, rate]);
    let over_pairs = {
        let inner = d.pi_fv(j_fv, nat, claim);
        d.pi_fv(i_fv, nat, inner)
    };

    let ty = {
        let t = d.arrow(hyp, over_pairs);
        let t = d.pi_fv(f_fv, seq_ty, t);
        d.pi_fv(m_fv, metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp, h);
        let t = d.lam_fv(f_fv, seq_ty, t);
        d.lam_fv(m_fv, metric_ty, t)
    };
    theorem(d, n.regular_seq_bound, ty, value)
}

// ---------------------------------------------------------------------------
// The carrier.
// ---------------------------------------------------------------------------

/// `Metric.CompletionSeq : Metric → Sort 1
///   := fun M => Subtype.{1} (Nat → M.carrier) (Metric.RegularSeq M)`.
///
/// Universe check, the same one `metric/subspace.rs` records: `M.carrier :
/// Sort 1`, so `Nat → M.carrier : Sort 1` and `Subtype.{1}` lands in
/// `Sort (max 1 1)`, definitionally `Sort 1` — exactly the carrier universe
/// `declare_record` fixes for `Metric`.
fn declare_completion_seq(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let s = space(d, c, p, n);
    let value = d.lam_fv(s.m_fv, s.metric_ty, s.sub_carrier);
    let ty = {
        let one = d.level_one();
        let sort_one = d.kernel().sort(one);
        d.arrow(s.metric_ty, sort_one)
    };
    definition(d, n.completion_seq, ty, value)
}

/// `Metric.completionSeq_carrier : ∀ M, Eq (Sort 1) (Metric.CompletionSeq M)
/// (Subtype (Nat → M.carrier) (Metric.RegularSeq M))` — `Eq.refl`.
fn declare_completion_seq_carrier(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let logic = c.rat.int.logic;
    let s = space(d, c, p, n);
    let one = d.level_one();
    let two = d.kernel().level_succ(one);
    let sort_one = d.kernel().sort(one);

    let lhs = d.const_app(n.completion_seq, &[s.m]);
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![two]);
        d.apply(head, &[sort_one, lhs, s.sub_carrier])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![two]);
        d.apply(head, &[sort_one, s.sub_carrier])
    };
    let ty = d.pi_fv(s.m_fv, s.metric_ty, stmt);
    let value = d.lam_fv(s.m_fv, s.metric_ty, proof);
    theorem(d, n.completion_seq_carrier, ty, value)
}

/// `Metric.completionVal : Π (M : Metric), Metric.CompletionSeq M → Nat →
/// M.carrier := fun M x => Subtype.val x`.
fn declare_completion_val(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let s = space(d, c, p, n);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let body = {
        let head = s.val_head;
        d.apply(head, &[x])
    };
    let value = {
        let t = d.lam_fv(x_fv, s.sub_carrier, body);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let completion = d.const_app(n.completion_seq, &[s.m]);
        let t = d.arrow(completion, s.seq_ty);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, n.completion_val, ty, value)
}

/// `Metric.completionRegular : ∀ M x, Metric.RegularSeq M
/// (Metric.completionVal M x)` — `Subtype.property`.
///
/// This is where the modulus comes back OUT as usable content, and the reason
/// the carrier had to fix it rather than existentially quantify it.
fn declare_completion_regular(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let logic = c.rat.int.logic;
    let s = space(d, c, p, n);
    let one = d.level_one();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let underlying = d.const_app(n.completion_val, &[s.m, x]);
    let stmt = {
        let head = s.regular_head;
        d.apply(head, &[underlying])
    };
    let proof = {
        let head = d.kernel().const_(logic.sigma.subtype_property, vec![one]);
        let seq_ty = s.seq_ty;
        let regular_head = s.regular_head;
        d.apply(head, &[seq_ty, regular_head, x])
    };
    let completion = d.const_app(n.completion_seq, &[s.m]);
    let ty = {
        let t = d.pi_fv(x_fv, completion, stmt);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(x_fv, completion, proof);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    theorem(d, n.completion_regular, ty, value)
}

// ---------------------------------------------------------------------------
// The distance SEQUENCE (not yet its limit).
// ---------------------------------------------------------------------------

/// `Metric.completionDistSeq : Π (M : Metric), CompletionSeq M →
/// CompletionSeq M → Nat → CReal
///   := fun M x y n => M.dist (completionVal M x n) (completionVal M y n)`.
///
/// **The object ADR-1625's reuse count got wrong.** It is a `Nat → CReal` for
/// a completely arbitrary `M`, so every `CReal.converges_*` theorem in
/// `creal/convergence.rs` instantiates at it — being "stated about `CReal`
/// alone" is the precondition for that, not a disqualification (ADR-1678
/// measurement 3).
fn declare_completion_dist_seq(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let s = space(d, c, p, n);
    let nat = d.nat_ty();
    let creal_ty = d.kernel().const_(c.creal, vec![]);
    let completion = d.const_app(n.completion_seq, &[s.m]);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let body = {
        let vx = d.const_app(n.completion_val, &[s.m, x, k]);
        let vy = d.const_app(n.completion_val, &[s.m, y, k]);
        let dist = field(d, p, s.m, DIST);
        d.apply(dist, &[vx, vy])
    };
    let value = {
        let t = d.lam_fv(k_fv, nat, body);
        let t = d.lam_fv(y_fv, completion, t);
        let t = d.lam_fv(x_fv, completion, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let t = d.arrow(nat, creal_ty);
        let t = d.arrow(completion, t);
        let t = d.arrow(completion, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, n.completion_dist_seq, ty, value)
}

/// `Metric.completionDistSeq_eval : ∀ M x y n, Eq CReal
/// (Metric.completionDistSeq M x y n)
/// (M.dist (Metric.completionVal M x n) (Metric.completionVal M y n))`
/// — `Eq.refl`.
fn declare_completion_dist_seq_eval(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let logic = c.rat.int.logic;
    let s = space(d, c, p, n);
    let one = d.level_one();
    let nat = d.nat_ty();
    let creal_ty = d.kernel().const_(c.creal, vec![]);
    let completion = d.const_app(n.completion_seq, &[s.m]);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let lhs = d.const_app(n.completion_dist_seq, &[s.m, x, y, k]);
    let rhs = {
        let vx = d.const_app(n.completion_val, &[s.m, x, k]);
        let vy = d.const_app(n.completion_val, &[s.m, y, k]);
        let dist = field(d, p, s.m, DIST);
        d.apply(dist, &[vx, vy])
    };
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        d.apply(head, &[creal_ty, lhs, rhs])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(head, &[creal_ty, rhs])
    };
    let ty = {
        let t = d.pi_fv(k_fv, nat, stmt);
        let t = d.pi_fv(y_fv, completion, t);
        let t = d.pi_fv(x_fv, completion, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(k_fv, nat, proof);
        let t = d.lam_fv(y_fv, completion, t);
        let t = d.lam_fv(x_fv, completion, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    theorem(d, n.completion_dist_seq_eval, ty, value)
}

// ---------------------------------------------------------------------------
// The embedding, at the level of sequences.
// ---------------------------------------------------------------------------

/// `Metric.embedSeq : Π (M : Metric), M.carrier → Metric.CompletionSeq M
///   := fun M a => Subtype.mk (fun _ => a) <regularity>`.
///
/// The regularity obligation is `∀ m n, d(a, a) ≤ 1/(m+1) + 1/(n+1)`, and the
/// proof is `Metric.dist_self` (giving `d(a,a) ~ 0`) transported across
/// `CReal.le_congr`-style rewriting into the nonnegativity of the rate. The
/// rate is `ofRat (1/(m+1) + 1/(n+1))`, nonnegative by
/// `CReal.of_rat_le_of_rat` against `Rat.zero_le_nat_div_succ` twice — no new
/// estimate at the metric level.
fn declare_embed_seq(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let logic = c.rat.int.logic;
    let s = space(d, c, p, n);
    let one = d.level_one();
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    // `fun _ : Nat => a`.
    let const_seq = {
        let ignored = d.fresh_fvar();
        d.lam_fv(ignored, nat, a)
    };

    // The regularity proof, at the constant sequence: `∀ m n, le (d a a)
    // (ofRat (1/(m+1) + 1/(n+1)))`.
    let regular_proof = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let one_nat = d.num(1);
        let qi = d.const_app(c.rat.nat_div_succ, &[one_nat, i]);
        let qj = d.const_app(c.rat.nat_div_succ, &[one_nat, j]);
        let q = radd(d, qi, qj);
        let rate = d.const_app(c.of_rat, &[q]);

        // `Rat.le Rat.zero (qi + qj)`: `Rat.add_le_add` gives `0 + 0 ≤ qi + qj`
        // and `Rat.add_zero Rat.zero : Eq (0 + 0) 0` rewrites the left side.
        let rat_zero = rzero(d, c.rat);
        let zero_le_q = {
            let zi = d.lemma(c.rat.zero_le_nat_div_succ, &[one_nat, i]);
            let zj = d.lemma(c.rat.zero_le_nat_div_succ, &[one_nat, j]);
            let summed = d.lemma(c.rat.add_le_add, &[rat_zero, qi, rat_zero, qj, zi, zj]);
            let padded = radd(d, rat_zero, rat_zero);
            let collapse = d.lemma(c.rat.add_zero, &[rat_zero]);
            rat_eq_rewrite(d, padded, rat_zero, collapse, summed, &|d, t| {
                rle(d, c.rat, t, q)
            })
        };

        // `CReal.zero` IS `CReal.ofRat Rat.zero`, so `CReal.ofRat_le` lands
        // directly on `le CReal.zero rate` with no bridging step.
        let zero_le_rate = d.lemma(c.of_rat_le, &[rat_zero, q, zero_le_q]);

        // `d a a ~ 0` (Metric.dist_self) turns `le 0 rate` into `le (d a a) rate`
        // through `CReal.le_congr`'s left slot.
        let self_zero = d.lemma(p.dist_self, &[s.m, a]);
        let zero_creal = d.kernel().const_(c.zero, vec![]);
        let dist = field(d, p, s.m, DIST);
        let daa = d.apply(dist, &[a, a]);
        let symm = d.lemma(c.equiv_symm, &[daa, zero_creal, self_zero]);
        let rate_refl = d.lemma(c.equiv_refl, &[rate]);
        let body = d.lemma(
            c.le_congr,
            &[zero_creal, daa, rate, rate, symm, rate_refl, zero_le_rate],
        );
        let inner = d.lam_fv(j_fv, nat, body);
        d.lam_fv(i_fv, nat, inner)
    };

    let body = {
        let head = d.kernel().const_(logic.sigma.subtype_mk, vec![one]);
        let seq_ty = s.seq_ty;
        let regular_head = s.regular_head;
        d.apply(head, &[seq_ty, regular_head, const_seq, regular_proof])
    };
    let value = {
        let t = d.lam_fv(a_fv, s.carrier, body);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let completion = d.const_app(n.completion_seq, &[s.m]);
        let t = d.arrow(s.carrier, completion);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, n.embed_seq, ty, value)
}

/// `Metric.embedSeq_val : ∀ M a n,
/// Eq M.carrier (Metric.completionVal M (Metric.embedSeq M a) n) a`
/// — `Eq.refl`, because `Subtype.val` ι-reduces on the literal constructor.
fn declare_embed_seq_val(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let logic = c.rat.int.logic;
    let s = space(d, c, p, n);
    let one = d.level_one();
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let embedded = d.const_app(n.embed_seq, &[s.m, a]);
    let lhs = d.const_app(n.completion_val, &[s.m, embedded, k]);
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        let carrier = s.carrier;
        d.apply(head, &[carrier, lhs, a])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        let carrier = s.carrier;
        d.apply(head, &[carrier, a])
    };
    let ty = {
        let t = d.pi_fv(k_fv, nat, stmt);
        let t = d.pi_fv(a_fv, s.carrier, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(k_fv, nat, proof);
        let t = d.lam_fv(a_fv, s.carrier, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    theorem(d, n.embed_seq_val, ty, value)
}

/// `Metric.embedSeq_dist : ∀ M a b n, Eq CReal
/// (Metric.completionDistSeq M (embedSeq M a) (embedSeq M b) n) (M.dist a b)`
/// — `Eq.refl`.
///
/// **The embedding is an isometry**, at the level this slice can state it: the
/// distance SEQUENCE between two embedded points is the constant sequence at
/// their distance, so whatever limit the completion's `dist` takes of it is
/// `M.dist a b` on the nose.
///
/// Stated with `Eq`, deliberately. The weaker `CReal.le (…) (M.dist a b)` is
/// also true and is what a merely NON-EXPANDING map would give; the
/// difference is invisible here and visible in
/// [`declare_embed_seq_reflects`], which the `le` form cannot prove.
fn declare_embed_seq_dist(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let logic = c.rat.int.logic;
    let s = space(d, c, p, n);
    let one = d.level_one();
    let nat = d.nat_ty();
    let creal_ty = d.kernel().const_(c.creal, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let ea = d.const_app(n.embed_seq, &[s.m, a]);
    let eb = d.const_app(n.embed_seq, &[s.m, b]);
    let lhs = d.const_app(n.completion_dist_seq, &[s.m, ea, eb, k]);
    let rhs = {
        let dist = field(d, p, s.m, DIST);
        d.apply(dist, &[a, b])
    };
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        d.apply(head, &[creal_ty, lhs, rhs])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(head, &[creal_ty, rhs])
    };
    let ty = {
        let t = d.pi_fv(k_fv, nat, stmt);
        let t = d.pi_fv(b_fv, s.carrier, t);
        let t = d.pi_fv(a_fv, s.carrier, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(k_fv, nat, proof);
        let t = d.lam_fv(b_fv, s.carrier, t);
        let t = d.lam_fv(a_fv, s.carrier, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    theorem(d, n.embed_seq_dist, ty, value)
}

/// `Metric.embedSeq_reflects : ∀ M a b,
/// (∀ n, CReal.Equiv (completionDistSeq M (embedSeq M a) (embedSeq M b) n)
///                   CReal.zero) → M.equiv a b`
/// — `fun M a b h => M.distEquiv a b (h Nat.zero)`.
///
/// **This is the theorem a non-expanding map cannot prove, and therefore the
/// one that makes [`declare_embed_seq_dist`]'s `Eq` load-bearing.** With only
/// `dist (embed a) (embed b) ≤ dist a b`, a hypothesis bounding the left side
/// by `0` says nothing about the right; with the equation, `h 0` IS a proof of
/// `CReal.Equiv (M.dist a b) CReal.zero` definitionally, and `M.distEquiv`
/// consumes it unchanged.
fn declare_embed_seq_reflects(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    n: MetricCompletionNames,
) -> Result<(), KernelError> {
    let s = space(d, c, p, n);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let ea = d.const_app(n.embed_seq, &[s.m, a]);
    let eb = d.const_app(n.embed_seq, &[s.m, b]);
    let zero = d.kernel().const_(c.zero, vec![]);

    let hyp = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sampled = d.const_app(n.completion_dist_seq, &[s.m, ea, eb, k]);
        let claim = d.const_app(c.equiv, &[sampled, zero]);
        d.pi_fv(k_fv, nat, claim)
    };
    let conclusion = {
        let equiv = field(d, p, s.m, EQUIV);
        d.apply(equiv, &[a, b])
    };

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let proof = {
        let zero_nat = d.num(0);
        let at_zero = d.apply(h, &[zero_nat]);
        let dist_equiv = field(d, p, s.m, DIST_EQUIV);
        d.apply(dist_equiv, &[a, b, at_zero])
    };

    let ty = {
        let t = d.arrow(hyp, conclusion);
        let t = d.pi_fv(b_fv, s.carrier, t);
        let t = d.pi_fv(a_fv, s.carrier, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp, proof);
        let t = d.lam_fv(b_fv, s.carrier, t);
        let t = d.lam_fv(a_fv, s.carrier, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    theorem(d, n.embed_seq_reflects, ty, value)
}

/// Build (or return, if already built) the `Metric.completion*` declarations.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub fn build_metric_completion_prelude(
    kernel: &mut Kernel,
) -> Result<MetricCompletionNames, KernelError> {
    let p = crate::build_metric_prelude(kernel)?;
    let creal = p.cpoint.creal;
    // The SAME interned `Metric` namespace `metric.rs`'s own `intern`
    // produces: name interning is content-addressed, so re-deriving it here
    // yields the same `NameId`.
    let metric_ns = {
        let root = kernel.anon();
        kernel.name_str(root, "Metric")
    };
    let n = intern(kernel, metric_ns);
    if kernel.environment().get(n.regular_seq).is_some() {
        return Ok(n);
    }

    let mut d = IntDev::new(kernel, creal.rat.int);
    declare_regular_seq(&mut d, p, n)?;
    declare_regular_seq_cauchy_at(&mut d, creal, p, n)?;
    declare_regular_seq_bound(&mut d, creal, p, n)?;
    declare_completion_seq(&mut d, creal, p, n)?;
    declare_completion_seq_carrier(&mut d, creal, p, n)?;
    declare_completion_val(&mut d, creal, p, n)?;
    declare_completion_regular(&mut d, creal, p, n)?;
    declare_completion_dist_seq(&mut d, creal, p, n)?;
    declare_completion_dist_seq_eval(&mut d, creal, p, n)?;
    declare_embed_seq(&mut d, creal, p, n)?;
    declare_embed_seq_val(&mut d, creal, p, n)?;
    declare_embed_seq_dist(&mut d, creal, p, n)?;
    declare_embed_seq_reflects(&mut d, creal, p, n)?;
    Ok(n)
}
