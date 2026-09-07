//! `AlgS.Ideal.*` — an **ideal** of an abstract `AlgS.CommRing`, and the
//! quotient ring `R/I`, built by the setoid route (ADR-1676).
//!
//! # Why this file exists
//!
//! Measured before the lane started: `ideal` occurred **zero** times in the
//! whole kernel source (positive control in the same sweep: 981 `AlgS.`
//! references). So did `subring`, `submodule`, `quotientRing`, `localiz`,
//! `tensor`, `irreducib` and `splitting`. The algebra shelf had a group
//! quotient (`AlgS.Hom.quotient`, ADR-1595) and a subgroup lattice
//! (`AlgS.Subgroup.*`, ADR-1609) but no ring-theoretic subobject at all.
//!
//! # An ideal is a predicate, and it is a subgroup plus exactly one field
//!
//! This kernel has no `Quot` (ADR-1595, settled policy) and the subobject
//! layer's decision is that a subobject is a **predicate**, not a carrier
//! (`AlgS.Hom.ker`, `AlgS.Hom.image`, `AlgS.Subgroup.IsSub` all do this).
//! `AlgS.Ideal.IsIdeal` follows it, so the ideal's five conjuncts line up
//! one-for-one with `AlgS.Subgroup.IsSub`'s four:
//!
//! | conjunct | free under `Eq`? | in `IsSub`? |
//! |---|---|---|
//! | `forall a b, R.equiv a b -> I a -> I b`      | **YES** (`Eq.subst`) | yes |
//! | `I R.zero`                                   | no | yes |
//! | `forall a b, I a -> I b -> I (R.add a b)`    | no | yes |
//! | `forall a, I a -> I (R.neg a)`               | no | yes |
//! | `forall r a, I a -> I (R.mul r a)`           | no | **no — this is the ideal** |
//!
//! So the measured cost of "ideal" over "additive subgroup" is **one field**,
//! and the setoid tax on the whole layer is the same **one field** it is for
//! subgroups.
//!
//! `closedNeg` is kept as an explicit conjunct even though it is DERIVABLE
//! from `absorb` (`-a ~ (-1) * a`, see [`declare_mul_neg_l`]). Keeping it
//! explicit is what makes the absorbing law's mutant *sharp*: with
//! `closedNeg` present, dropping `absorb` breaks the quotient's
//! **multiplicative** congruence and nothing else. Deriving it instead would
//! have made the same mutant also break `equivSymm`, and a mutant that
//! breaks everything localizes nothing.
//!
//! # `R/I` is the same carrier under a coarser equivalence
//!
//! `AlgS.Ideal.quotient R I hI : AlgS.CommRing` has `carrier := R.carrier`
//! and `equiv := fun x y => I (R.add x (R.neg y))` — exactly the shape
//! `AlgS.Hom.quotient` uses for groups, and for the same reason: with no
//! `Quot` there is no type of cosets to build. Everything a real `Quot`
//! would supply for free is an explicit field here, and the split is the
//! deliverable:
//!
//! | the quotient's 23 fields | how discharged | count |
//! |---|---|---|
//! | carrier, zero, one, add, mul, neg | `R`'s own, unchanged | 6 |
//! | equiv | the ideal-coset relation | 1 |
//! | equivRefl/Symm/Trans | proved: `negAdd`; `closedNeg`+`negAddDist`; `closedAdd` | 3 |
//! | addCongr | proved: `closedAdd` + `addSwapMid` + `negAddDist` | 1 |
//! | mulCongr | proved: **`absorb` twice** + `closedAdd` + regrouping | 1 |
//! | negCongr | proved: `closedNeg` + `negAddDist` (one `respects`) | 1 |
//! | the ten LAW fields | all free, through `AlgS.Ideal.ofEquiv` | 10 |
//!
//! The ten law fields being free is the load-bearing observation: an ideal
//! coset relation is COARSER than `R.equiv`, so `AlgS.Ideal.ofEquiv` (a
//! four-step proof) turns every law `R` already has into the same law for
//! `R/I`, and no ring law is re-proved.

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;

use super::structures::{self, RecordNames, app2, arrow, lam_over, pi_over, sel};
use super::structures_setoid::idx;

// ---------------------------------------------------------------------------
// Free-variable block 29_xxx — disjoint from 21_xxx (`AlgS.Hom`), 24_xxx
// (`AlgS.Subgroup`) and every other block in use crate-wide.
// ---------------------------------------------------------------------------

const R_FV: u64 = 29_000;
const I_FV: u64 = 29_001;
const HI_FV: u64 = 29_002;
const A_FV: u64 = 29_010;
const B_FV: u64 = 29_011;
const C_FV: u64 = 29_012;
const X_FV: u64 = 29_013;
const Y_FV: u64 = 29_014;
const Z_FV: u64 = 29_015;
const AP_FV: u64 = 29_016;
const BP_FV: u64 = 29_017;
const H1_FV: u64 = 29_020;
const H2_FV: u64 = 29_021;
const W_FV: u64 = 29_030;
const HW_FV: u64 = 29_031;
const W2_FV: u64 = 29_032;
const HW2_FV: u64 = 29_033;
const MOT_FV: u64 = 29_040;
/// The principal ideal's GENERATOR. Deliberately outside the range
/// [`five_stmts`] binds (`A_FV`/`B_FV`/`X_FV`/`H1_FV`/`H2_FV`): the generator
/// stays free while a conjunct's own binders are abstracted around it, so
/// sharing one id makes the statement's `pi_over` swallow the generator.
const G_FV: u64 = 29_050;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

// ---------------------------------------------------------------------------
// The ambient commutative ring's selectors, resolved once.
// ---------------------------------------------------------------------------

struct RCtx {
    r: ExprId,
    ring_ty: ExprId,
    carrier: ExprId,
    equiv: ExprId,
    refl: ExprId,
    symm: ExprId,
    trans: ExprId,
    zero: ExprId,
    one: ExprId,
    add: ExprId,
    mul: ExprId,
    add_congr: ExprId,
    mul_congr: ExprId,
    add_assoc: ExprId,
    add_comm: ExprId,
    add_zero: ExprId,
    mul_assoc: ExprId,
    mul_one_l: ExprId,
    mul_one_r: ExprId,
    distrib_l: ExprId,
    distrib_r: ExprId,
    neg: ExprId,
    neg_congr: ExprId,
    neg_add: ExprId,
    mul_comm: ExprId,
    /// `R.carrier -> Prop`, the type of an ideal predicate.
    pred_ty: ExprId,
}

fn rctx(k: &mut Kernel, cr: &RecordNames) -> RCtx {
    use idx::comm_ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_CONGR, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, EQUIV,
        EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, MUL, MUL_ASSOC, MUL_COMM, MUL_CONGR, MUL_ONE_L,
        MUL_ONE_R, NEG, NEG_ADD, NEG_CONGR, ONE, ZERO,
    };
    let ring_ty = k.const_(cr.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, cr, CARRIER, r);
    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let pred_ty = arrow(k, carrier, prop);
    RCtx {
        r,
        ring_ty,
        carrier,
        equiv: sel(k, cr, EQUIV, r),
        refl: sel(k, cr, EQUIV_REFL, r),
        symm: sel(k, cr, EQUIV_SYMM, r),
        trans: sel(k, cr, EQUIV_TRANS, r),
        zero: sel(k, cr, ZERO, r),
        one: sel(k, cr, ONE, r),
        add: sel(k, cr, ADD, r),
        mul: sel(k, cr, MUL, r),
        add_congr: sel(k, cr, ADD_CONGR, r),
        mul_congr: sel(k, cr, MUL_CONGR, r),
        add_assoc: sel(k, cr, ADD_ASSOC, r),
        add_comm: sel(k, cr, ADD_COMM, r),
        add_zero: sel(k, cr, ADD_ZERO, r),
        mul_assoc: sel(k, cr, MUL_ASSOC, r),
        mul_one_l: sel(k, cr, MUL_ONE_L, r),
        mul_one_r: sel(k, cr, MUL_ONE_R, r),
        distrib_l: sel(k, cr, DISTRIB_L, r),
        distrib_r: sel(k, cr, DISTRIB_R, r),
        neg: sel(k, cr, NEG, r),
        neg_congr: sel(k, cr, NEG_CONGR, r),
        neg_add: sel(k, cr, NEG_ADD, r),
        mul_comm: sel(k, cr, MUL_COMM, r),
        pred_ty,
    }
}

impl RCtx {
    fn eqv(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.equiv, a, b)
    }
    fn rf(&self, k: &mut Kernel, a: ExprId) -> ExprId {
        k.app(self.refl, a)
    }
    fn sy(&self, k: &mut Kernel, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        t_app(k, self.symm, &[a, b, h])
    }
    fn tr(
        &self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        t_app(k, self.trans, &[a, b, c, h1, h2])
    }
    fn pl(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.add, a, b)
    }
    fn tm(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.mul, a, b)
    }
    fn ng(&self, k: &mut Kernel, a: ExprId) -> ExprId {
        k.app(self.neg, a)
    }
    /// `R.addCongr a a' b b' ha hb`.
    #[allow(clippy::too_many_arguments)]
    fn addc(
        &self,
        k: &mut Kernel,
        a: ExprId,
        ap: ExprId,
        b: ExprId,
        bp: ExprId,
        ha: ExprId,
        hb: ExprId,
    ) -> ExprId {
        t_app(k, self.add_congr, &[a, ap, b, bp, ha, hb])
    }
    #[allow(clippy::too_many_arguments)]
    fn mulc(
        &self,
        k: &mut Kernel,
        a: ExprId,
        ap: ExprId,
        b: ExprId,
        bp: ExprId,
        ha: ExprId,
        hb: ExprId,
    ) -> ExprId {
        t_app(k, self.mul_congr, &[a, ap, b, bp, ha, hb])
    }
    fn negc(&self, k: &mut Kernel, a: ExprId, ap: ExprId, h: ExprId) -> ExprId {
        t_app(k, self.neg_congr, &[a, ap, h])
    }
}

/// A left-to-right equivalence chain: carries `a ~ b` and extends it on the
/// right. Every multi-step proof below is written as one of these, so a
/// reader can check the mathematics without reading `equivTrans` plumbing.
struct Chain {
    a: ExprId,
    b: ExprId,
    p: ExprId,
}

impl Chain {
    fn start(k: &mut Kernel, c: &RCtx, a: ExprId) -> Chain {
        let p = c.rf(k, a);
        Chain { a, b: a, p }
    }
    /// Extend by `q : b ~ next`.
    fn step(&mut self, k: &mut Kernel, c: &RCtx, next: ExprId, q: ExprId) {
        self.p = c.tr(k, self.a, self.b, next, self.p, q);
        self.b = next;
    }
}

/// Close a statement/value over `R` alone.
fn close_r(k: &mut Kernel, c: &RCtx, body: ExprId, lam: bool) -> ExprId {
    if lam {
        lam_over(k, R_FV, c.ring_ty, body)
    } else {
        pi_over(k, R_FV, c.ring_ty, body)
    }
}

/// Close over `R I` (a ring and an ideal predicate on it).
fn close_ri(k: &mut Kernel, c: &RCtx, body: ExprId, lam: bool) -> ExprId {
    let t = if lam {
        lam_over(k, I_FV, c.pred_ty, body)
    } else {
        pi_over(k, I_FV, c.pred_ty, body)
    };
    close_r(k, c, t, lam)
}

/// Close over `R I hI` — the three binders every quotient declaration needs.
fn close_rih(k: &mut Kernel, c: &RCtx, hi_ty: ExprId, body: ExprId, lam: bool) -> ExprId {
    let t = if lam {
        lam_over(k, HI_FV, hi_ty, body)
    } else {
        pi_over(k, HI_FV, hi_ty, body)
    };
    close_ri(k, c, t, lam)
}

fn theorem(
    k: &mut Kernel,
    ns: NameId,
    suffix: &str,
    ty: ExprId,
    value: ExprId,
) -> Result<NameId, KernelError> {
    let name = k.name_str(ns, suffix);
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

fn definition(
    k: &mut Kernel,
    ns: NameId,
    suffix: &str,
    ty: ExprId,
    value: ExprId,
) -> Result<NameId, KernelError> {
    let name = k.name_str(ns, suffix);
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// Nine generic `AlgS.CommRing` lemmas this construction needs and the spine
// does not have. `AlgS.mul_zero`/`AlgS.mul_neg_one` live over `AlgS.Ring`,
// so they are reached through `AlgS.CommRing.toRingS` (whose selectors
// iota-reduce to `R`'s own, the same route `field_setoid` uses).
// ---------------------------------------------------------------------------

/// Dependencies this module borrows from [`super::structures_setoid`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IdealDeps {
    /// `AlgS.CommRing.toRingS : AlgS.CommRing -> AlgS.Ring`.
    pub comm_ring_to_ring_s: NameId,
    /// `AlgS.mul_zero : forall (R : Ring) a, R.equiv (R.mul a R.zero) R.zero`.
    pub mul_zero: NameId,
    /// `AlgS.mul_neg_one : forall (R : Ring) x,
    /// R.equiv (R.mul x (R.neg R.one)) (R.neg x)`.
    pub mul_neg_one: NameId,
    /// `AlgS.neg_neg : forall (R : Ring) a, R.equiv (R.neg (R.neg a)) a`.
    pub neg_neg: NameId,
}

/// `AlgS.Ring`-level lemma `thm` applied at `AlgS.CommRing.toRingS R`.
fn at_ring(k: &mut Kernel, c: &RCtx, deps: &IdealDeps, thm: NameId) -> ExprId {
    let to_ring = k.const_(deps.comm_ring_to_ring_s, vec![]);
    let ring = k.app(to_ring, c.r);
    let t = k.const_(thm, vec![]);
    k.app(t, ring)
}

/// `AlgS.Ideal.zeroAdd : forall R a, R.equiv (R.add R.zero a) a`.
fn declare_zero_add(k: &mut Kernel, cr: &RecordNames, ns: NameId) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let a = k.fvar(A_FV);
    let lhs = c.pl(k, c.zero, a);
    let rhs = c.pl(k, a, c.zero);
    let mut ch = Chain::start(k, &c, lhs);
    let s1 = t_app(k, c.add_comm, &[c.zero, a]);
    ch.step(k, &c, rhs, s1);
    let s2 = k.app(c.add_zero, a);
    ch.step(k, &c, a, s2);

    let concl = c.eqv(k, lhs, a);
    let ty = pi_over(k, A_FV, c.carrier, concl);
    let ty = close_r(k, &c, ty, false);
    let value = lam_over(k, A_FV, c.carrier, ch.p);
    let value = close_r(k, &c, value, true);
    theorem(k, ns, "zeroAdd", ty, value)
}

/// `AlgS.Ideal.negAddL : forall R a, R.equiv (R.add (R.neg a) a) R.zero` —
/// the mirror of the record's own `negAdd` field, which is stated on the
/// right (`a + (-a) ~ 0`) only.
fn declare_neg_add_l(k: &mut Kernel, cr: &RecordNames, ns: NameId) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let a = k.fvar(A_FV);
    let na = c.ng(k, a);
    let lhs = c.pl(k, na, a);
    let mid = c.pl(k, a, na);
    let mut ch = Chain::start(k, &c, lhs);
    let s1 = t_app(k, c.add_comm, &[na, a]);
    ch.step(k, &c, mid, s1);
    let s2 = k.app(c.neg_add, a);
    ch.step(k, &c, c.zero, s2);

    let concl = c.eqv(k, lhs, c.zero);
    let ty = pi_over(k, A_FV, c.carrier, concl);
    let ty = close_r(k, &c, ty, false);
    let value = lam_over(k, A_FV, c.carrier, ch.p);
    let value = close_r(k, &c, value, true);
    theorem(k, ns, "negAddL", ty, value)
}

/// `AlgS.Ideal.negZero : forall R, R.equiv (R.neg R.zero) R.zero`.
fn declare_neg_zero(
    k: &mut Kernel,
    cr: &RecordNames,
    zero_add: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let nz = c.ng(k, c.zero);
    let sum = c.pl(k, c.zero, nz);
    let mut ch = Chain::start(k, &c, nz);
    // `-0 ~ 0 + (-0)`, by symm of `zeroAdd (-0)`.
    let za = {
        let t = k.const_(zero_add, vec![]);
        t_app(k, t, &[c.r, nz])
    };
    let s1 = c.sy(k, sum, nz, za);
    ch.step(k, &c, sum, s1);
    let s2 = k.app(c.neg_add, c.zero);
    ch.step(k, &c, c.zero, s2);

    let concl = c.eqv(k, nz, c.zero);
    let ty = close_r(k, &c, concl, false);
    let value = close_r(k, &c, ch.p, true);
    theorem(k, ns, "negZero", ty, value)
}

/// `AlgS.Ideal.zeroMul : forall R a, R.equiv (R.mul R.zero a) R.zero`.
fn declare_zero_mul(
    k: &mut Kernel,
    cr: &RecordNames,
    deps: &IdealDeps,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let a = k.fvar(A_FV);
    let lhs = c.tm(k, c.zero, a);
    let mid = c.tm(k, a, c.zero);
    let mut ch = Chain::start(k, &c, lhs);
    let s1 = t_app(k, c.mul_comm, &[c.zero, a]);
    ch.step(k, &c, mid, s1);
    let mz = at_ring(k, &c, deps, deps.mul_zero);
    let s2 = k.app(mz, a);
    ch.step(k, &c, c.zero, s2);

    let concl = c.eqv(k, lhs, c.zero);
    let ty = pi_over(k, A_FV, c.carrier, concl);
    let ty = close_r(k, &c, ty, false);
    let value = lam_over(k, A_FV, c.carrier, ch.p);
    let value = close_r(k, &c, value, true);
    theorem(k, ns, "zeroMul", ty, value)
}

/// `AlgS.Ideal.mulNegR : forall R a b,
/// R.equiv (R.mul a (R.neg b)) (R.neg (R.mul a b))`.
fn declare_mul_neg_r(
    k: &mut Kernel,
    cr: &RecordNames,
    deps: &IdealDeps,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let mno = at_ring(k, &c, deps, deps.mul_neg_one);
    let none = c.ng(k, c.one);

    let nb = c.ng(k, b);
    let lhs = c.tm(k, a, nb);
    let b_none = c.tm(k, b, none);
    let a_b_none = c.tm(k, a, b_none);
    let ab = c.tm(k, a, b);
    let ab_none = c.tm(k, ab, none);
    let nab = c.ng(k, ab);

    let mut ch = Chain::start(k, &c, lhs);
    // `a * (-b) ~ a * (b * (-1))`
    let mno_b = k.app(mno, b);
    let s0 = c.sy(k, b_none, nb, mno_b);
    let ra = c.rf(k, a);
    let s1 = c.mulc(k, a, a, nb, b_none, ra, s0);
    ch.step(k, &c, a_b_none, s1);
    // `a * (b * (-1)) ~ (a * b) * (-1)`
    let assoc = t_app(k, c.mul_assoc, &[a, b, none]);
    let s2 = c.sy(k, ab_none, a_b_none, assoc);
    ch.step(k, &c, ab_none, s2);
    // `(a * b) * (-1) ~ -(a * b)`
    let s3 = k.app(mno, ab);
    ch.step(k, &c, nab, s3);

    let concl = c.eqv(k, lhs, nab);
    let ty = pi_over(k, B_FV, c.carrier, concl);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = close_r(k, &c, ty, false);
    let value = lam_over(k, B_FV, c.carrier, ch.p);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = close_r(k, &c, value, true);
    theorem(k, ns, "mulNegR", ty, value)
}

/// `AlgS.Ideal.mulNegL : forall R a b,
/// R.equiv (R.mul (R.neg a) b) (R.neg (R.mul a b))`.
fn declare_mul_neg_l(
    k: &mut Kernel,
    cr: &RecordNames,
    mul_neg_r: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let na = c.ng(k, a);
    let lhs = c.tm(k, na, b);
    let b_na = c.tm(k, b, na);
    let ba = c.tm(k, b, a);
    let nba = c.ng(k, ba);
    let ab = c.tm(k, a, b);
    let nab = c.ng(k, ab);

    let mut ch = Chain::start(k, &c, lhs);
    let s1 = t_app(k, c.mul_comm, &[na, b]);
    ch.step(k, &c, b_na, s1);
    let s2 = {
        let t = k.const_(mul_neg_r, vec![]);
        t_app(k, t, &[c.r, b, a])
    };
    ch.step(k, &c, nba, s2);
    let comm_ba = t_app(k, c.mul_comm, &[b, a]);
    let s3 = c.negc(k, ba, ab, comm_ba);
    ch.step(k, &c, nab, s3);

    let concl = c.eqv(k, lhs, nab);
    let ty = pi_over(k, B_FV, c.carrier, concl);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = close_r(k, &c, ty, false);
    let value = lam_over(k, B_FV, c.carrier, ch.p);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = close_r(k, &c, value, true);
    theorem(k, ns, "mulNegL", ty, value)
}

/// `AlgS.Ideal.negAddDist : forall R a b,
/// R.equiv (R.neg (R.add a b)) (R.add (R.neg a) (R.neg b))`.
///
/// Three steps, through `-1`: `-(a+b) ~ (a+b)*(-1) ~ a*(-1) + b*(-1) ~
/// (-a) + (-b)`. The obvious additive route (build `(a+b) + ((-a)+(-b)) ~ 0`
/// and cancel) is thirteen.
fn declare_neg_add_dist(
    k: &mut Kernel,
    cr: &RecordNames,
    deps: &IdealDeps,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let mno = at_ring(k, &c, deps, deps.mul_neg_one);
    let none = c.ng(k, c.one);

    let ab = c.pl(k, a, b);
    let nab = c.ng(k, ab);
    let ab_none = c.tm(k, ab, none);
    let a_none = c.tm(k, a, none);
    let b_none = c.tm(k, b, none);
    let split = c.pl(k, a_none, b_none);
    let na = c.ng(k, a);
    let nb = c.ng(k, b);
    let rhs = c.pl(k, na, nb);

    let mut ch = Chain::start(k, &c, nab);
    let mno_ab = k.app(mno, ab);
    let s1 = c.sy(k, ab_none, nab, mno_ab);
    ch.step(k, &c, ab_none, s1);
    let s2 = t_app(k, c.distrib_r, &[a, b, none]);
    ch.step(k, &c, split, s2);
    let mno_a = k.app(mno, a);
    let mno_b = k.app(mno, b);
    let s3 = c.addc(k, a_none, na, b_none, nb, mno_a, mno_b);
    ch.step(k, &c, rhs, s3);

    let concl = c.eqv(k, nab, rhs);
    let ty = pi_over(k, B_FV, c.carrier, concl);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = close_r(k, &c, ty, false);
    let value = lam_over(k, B_FV, c.carrier, ch.p);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = close_r(k, &c, value, true);
    theorem(k, ns, "negAddDist", ty, value)
}

/// `AlgS.Ideal.addSwapMid : forall R a x b y,
/// R.equiv ((a + x) + (b + y)) ((a + b) + (x + y))` — the abelian-group
/// rearrangement the quotient's `addCongr` needs.
fn declare_add_swap_mid(
    k: &mut Kernel,
    cr: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let a = k.fvar(A_FV);
    let x = k.fvar(X_FV);
    let b = k.fvar(B_FV);
    let y = k.fvar(Y_FV);

    let ax = c.pl(k, a, x);
    let by = c.pl(k, b, y);
    let lhs = c.pl(k, ax, by);
    let x_by = c.pl(k, x, by);
    let a_x_by = c.pl(k, a, x_by);
    let xb = c.pl(k, x, b);
    let xb_y = c.pl(k, xb, y);
    let bx = c.pl(k, b, x);
    let bx_y = c.pl(k, bx, y);
    let xy = c.pl(k, x, y);
    let b_xy = c.pl(k, b, xy);
    let a_b_xy = c.pl(k, a, b_xy);
    let ab = c.pl(k, a, b);
    let rhs = c.pl(k, ab, xy);

    // inner : `x + (b + y) ~ b + (x + y)`
    let inner = {
        let mut ic = Chain::start(k, &c, x_by);
        let assoc = t_app(k, c.add_assoc, &[x, b, y]);
        let i1 = c.sy(k, xb_y, x_by, assoc);
        ic.step(k, &c, xb_y, i1);
        let comm = t_app(k, c.add_comm, &[x, b]);
        let ry = c.rf(k, y);
        let i2 = c.addc(k, xb, bx, y, y, comm, ry);
        ic.step(k, &c, bx_y, i2);
        let i3 = t_app(k, c.add_assoc, &[b, x, y]);
        ic.step(k, &c, b_xy, i3);
        ic.p
    };

    let mut ch = Chain::start(k, &c, lhs);
    let s1 = t_app(k, c.add_assoc, &[a, x, by]);
    ch.step(k, &c, a_x_by, s1);
    let ra = c.rf(k, a);
    let s2 = c.addc(k, a, a, x_by, b_xy, ra, inner);
    ch.step(k, &c, a_b_xy, s2);
    let assoc2 = t_app(k, c.add_assoc, &[a, b, xy]);
    let s3 = c.sy(k, rhs, a_b_xy, assoc2);
    ch.step(k, &c, rhs, s3);

    let concl = c.eqv(k, lhs, rhs);
    let ty = pi_over(k, Y_FV, c.carrier, concl);
    let ty = pi_over(k, B_FV, c.carrier, ty);
    let ty = pi_over(k, X_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = close_r(k, &c, ty, false);
    let value = lam_over(k, Y_FV, c.carrier, ch.p);
    let value = lam_over(k, B_FV, c.carrier, value);
    let value = lam_over(k, X_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = close_r(k, &c, value, true);
    theorem(k, ns, "addSwapMid", ty, value)
}

/// `AlgS.Ideal.addRegroup : forall R p u v w,
/// R.equiv ((p + u) + (v + w)) (p + ((u + v) + w))` — the regrouping the
/// quotient's `mulCongr` needs to expose the cancelling pair `u + v`.
fn declare_add_regroup(
    k: &mut Kernel,
    cr: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let p = k.fvar(A_FV);
    let u = k.fvar(X_FV);
    let v = k.fvar(Y_FV);
    let w = k.fvar(Z_FV);

    let pu = c.pl(k, p, u);
    let vw = c.pl(k, v, w);
    let lhs = c.pl(k, pu, vw);
    let u_vw = c.pl(k, u, vw);
    let p_u_vw = c.pl(k, p, u_vw);
    let uv = c.pl(k, u, v);
    let uv_w = c.pl(k, uv, w);
    let rhs = c.pl(k, p, uv_w);

    let mut ch = Chain::start(k, &c, lhs);
    let s1 = t_app(k, c.add_assoc, &[p, u, vw]);
    ch.step(k, &c, p_u_vw, s1);
    let assoc = t_app(k, c.add_assoc, &[u, v, w]);
    let inner = c.sy(k, uv_w, u_vw, assoc);
    let rp = c.rf(k, p);
    let s2 = c.addc(k, p, p, u_vw, uv_w, rp, inner);
    ch.step(k, &c, rhs, s2);

    let concl = c.eqv(k, lhs, rhs);
    let ty = pi_over(k, Z_FV, c.carrier, concl);
    let ty = pi_over(k, Y_FV, c.carrier, ty);
    let ty = pi_over(k, X_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = close_r(k, &c, ty, false);
    let value = lam_over(k, Z_FV, c.carrier, ch.p);
    let value = lam_over(k, Y_FV, c.carrier, value);
    let value = lam_over(k, X_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = close_r(k, &c, value, true);
    theorem(k, ns, "addRegroup", ty, value)
}

// ---------------------------------------------------------------------------
// `AlgS.Ideal.IsIdeal` — five conjuncts, and the `And` plumbing over them.
// ---------------------------------------------------------------------------

/// `forall a b, R.equiv a b -> I a -> I b` — **the setoid-only obligation**,
/// the same one `AlgS.Subgroup.IsSub` carries and an `Eq`-flavored spine
/// would get free from `Eq.subst`.
fn respects_stmt(k: &mut Kernel, c: &RCtx, i: ExprId) -> ExprId {
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let hyp1 = c.eqv(k, a, b);
    let hyp2 = k.app(i, a);
    let concl = k.app(i, b);
    let t = pi_over(k, H2_FV, hyp2, concl);
    let t = pi_over(k, H1_FV, hyp1, t);
    let t = pi_over(k, B_FV, c.carrier, t);
    pi_over(k, A_FV, c.carrier, t)
}

/// `I R.zero`.
fn mem_zero_stmt(k: &mut Kernel, c: &RCtx, i: ExprId) -> ExprId {
    k.app(i, c.zero)
}

/// `forall a b, I a -> I b -> I (R.add a b)`.
fn closed_add_stmt(k: &mut Kernel, c: &RCtx, i: ExprId) -> ExprId {
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let hyp1 = k.app(i, a);
    let hyp2 = k.app(i, b);
    let ab = c.pl(k, a, b);
    let concl = k.app(i, ab);
    let t = pi_over(k, H2_FV, hyp2, concl);
    let t = pi_over(k, H1_FV, hyp1, t);
    let t = pi_over(k, B_FV, c.carrier, t);
    pi_over(k, A_FV, c.carrier, t)
}

/// `forall a, I a -> I (R.neg a)`.
fn closed_neg_stmt(k: &mut Kernel, c: &RCtx, i: ExprId) -> ExprId {
    let a = k.fvar(A_FV);
    let hyp = k.app(i, a);
    let na = c.ng(k, a);
    let concl = k.app(i, na);
    let t = pi_over(k, H1_FV, hyp, concl);
    pi_over(k, A_FV, c.carrier, t)
}

/// `forall r a, I a -> I (R.mul r a)` — **the absorbing law: the one field
/// that separates an ideal from an additive subgroup.**
fn absorb_stmt(k: &mut Kernel, c: &RCtx, i: ExprId) -> ExprId {
    let s = k.fvar(X_FV);
    let a = k.fvar(A_FV);
    let hyp = k.app(i, a);
    let sa = c.tm(k, s, a);
    let concl = k.app(i, sa);
    let t = pi_over(k, H1_FV, hyp, concl);
    let t = pi_over(k, A_FV, c.carrier, t);
    pi_over(k, X_FV, c.carrier, t)
}

const N_CONJ: usize = 5;

fn five_stmts(k: &mut Kernel, c: &RCtx, i: ExprId) -> [ExprId; N_CONJ] {
    [
        respects_stmt(k, c, i),
        mem_zero_stmt(k, c, i),
        closed_add_stmt(k, c, i),
        closed_neg_stmt(k, c, i),
        absorb_stmt(k, c, i),
    ]
}

/// `And p0 (And p1 (And p2 (And p3 p4)))`.
fn nest_and(k: &mut Kernel, lg: &LogicPrelude, props: &[ExprId; N_CONJ]) -> ExprId {
    let and_c = k.const_(lg.and, vec![]);
    let mut acc = props[N_CONJ - 1];
    for p in props[..N_CONJ - 1].iter().rev() {
        acc = app2(k, and_c, *p, acc);
    }
    acc
}

/// The `And.intro` chain matching [`nest_and`].
fn intro_and(
    k: &mut Kernel,
    lg: &LogicPrelude,
    props: &[ExprId; N_CONJ],
    proofs: &[ExprId; N_CONJ],
) -> ExprId {
    let and_c = k.const_(lg.and, vec![]);
    let mut tail_prop = props[N_CONJ - 1];
    let mut tail_val = proofs[N_CONJ - 1];
    for i in (0..N_CONJ - 1).rev() {
        let and_intro = k.const_(lg.and_intro, vec![]);
        tail_val = t_app(k, and_intro, &[props[i], tail_prop, proofs[i], tail_val]);
        tail_prop = app2(k, and_c, props[i], tail_prop);
    }
    tail_val
}

/// Project conjunct `which` out of a proof of [`nest_and`].
fn project_and(
    k: &mut Kernel,
    lg: &LogicPrelude,
    props: &[ExprId; N_CONJ],
    h: ExprId,
    which: usize,
) -> ExprId {
    let and_c = k.const_(lg.and, vec![]);
    // `tails[i]` is what remains after `i` `And.right`s.
    let mut tails = vec![props[N_CONJ - 1]];
    for p in props[..N_CONJ - 1].iter().rev() {
        let last = *tails.last().expect("non-empty");
        tails.push(app2(k, and_c, *p, last));
    }
    tails.reverse();

    let mut cur = h;
    for (i, prop) in props.iter().enumerate().take(which) {
        let and_right = k.const_(lg.and_right, vec![]);
        cur = t_app(k, and_right, &[*prop, tails[i + 1], cur]);
    }
    if which == N_CONJ - 1 {
        cur
    } else {
        let and_left = k.const_(lg.and_left, vec![]);
        t_app(k, and_left, &[props[which], tails[which + 1], cur])
    }
}

/// `AlgS.Ideal.IsIdeal : forall (R : AlgS.CommRing),
/// (R.carrier -> Prop) -> Prop`.
fn declare_is_ideal(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let props = five_stmts(k, &c, i);
    let body = nest_and(k, lg, &props);
    let value = close_ri(k, &c, body, true);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = arrow(k, c.pred_ty, prop);
    let ty = close_r(k, &c, ty, false);

    definition(k, ns, "IsIdeal", ty, value)
}

/// `IsIdeal R I` as a term, over the `R`/`I` free variables.
fn is_ideal_at(k: &mut Kernel, c: &RCtx, is_ideal: NameId, i: ExprId) -> ExprId {
    let t = k.const_(is_ideal, vec![]);
    app2(k, t, c.r, i)
}

fn declare_accessor(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    is_ideal: NameId,
    which: usize,
    suffix: &str,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let props = five_stmts(k, &c, i);
    let hyp_ty = is_ideal_at(k, &c, is_ideal, i);
    let h = k.fvar(HI_FV);
    let proof = project_and(k, lg, &props, h, which);

    let value = close_rih(k, &c, hyp_ty, proof, true);
    let ty = close_rih(k, &c, hyp_ty, props[which], false);
    theorem(k, ns, suffix, ty, value)
}

/// The five accessor names, threaded through the quotient proofs.
#[derive(Debug, Clone, Copy)]
struct AccNames {
    respects: NameId,
    mem_zero: NameId,
    closed_add: NameId,
    closed_neg: NameId,
    absorb: NameId,
}

/// `<acc> R I hI` for an accessor already declared.
fn acc_at(k: &mut Kernel, c: &RCtx, name: NameId, i: ExprId, hi: ExprId) -> ExprId {
    let t = k.const_(name, vec![]);
    t_app(k, t, &[c.r, i, hi])
}

// ---------------------------------------------------------------------------
// Three instances, so the predicate is not vacuous: `bot`, `top`, and the
// principal ideal `(g)`.
// ---------------------------------------------------------------------------

/// `AlgS.Ideal.bot R := fun x => R.equiv x R.zero` — the ZERO ideal.
///
/// **Not the singleton `{0}`**: over a setoid the smallest ideal is the
/// equivalence CLASS of zero, because an ideal must be closed under
/// `R.equiv` (`IsIdeal`'s first conjunct). Same reasoning, and the same
/// shape, as `AlgS.Subgroup.bot`.
fn declare_bot(k: &mut Kernel, cr: &RecordNames, ns: NameId) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let x = k.fvar(X_FV);
    let body = c.eqv(k, x, c.zero);
    let body = lam_over(k, X_FV, c.carrier, body);
    let value = close_r(k, &c, body, true);
    let ty = close_r(k, &c, c.pred_ty, false);
    definition(k, ns, "bot", ty, value)
}

/// `AlgS.Ideal.top R := fun _ => True` — the whole ring, as an ideal.
fn declare_top(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let true_c = k.const_(lg.true_, vec![]);
    let body = lam_over(k, X_FV, c.carrier, true_c);
    let value = close_r(k, &c, body, true);
    let ty = close_r(k, &c, c.pred_ty, false);
    definition(k, ns, "top", ty, value)
}

/// `AlgS.Ideal.principal R g := fun x => Exists R.carrier
/// (fun r => R.equiv x (R.mul r g))` — the principal ideal `(g)`.
fn declare_principal(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    cr: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let g = k.fvar(A_FV);
    let x = k.fvar(X_FV);
    let r = k.fvar(W_FV);
    let rg = c.tm(k, r, g);
    let inner = c.eqv(k, x, rg);
    let pred = lam_over(k, W_FV, c.carrier, inner);
    let ex = k.const_(lg.exists_, vec![l1]);
    let body = t_app(k, ex, &[c.carrier, pred]);
    let body = lam_over(k, X_FV, c.carrier, body);
    let value = lam_over(k, A_FV, c.carrier, body);
    let value = close_r(k, &c, value, true);

    let ty = pi_over(k, A_FV, c.carrier, c.pred_ty);
    let ty = close_r(k, &c, ty, false);
    definition(k, ns, "principal", ty, value)
}

// -- `Exists` plumbing ------------------------------------------------------

fn ex_of(k: &mut Kernel, lg: &LogicPrelude, l1: LevelId, elem: ExprId, pred: ExprId) -> ExprId {
    let ex = k.const_(lg.exists_, vec![l1]);
    t_app(k, ex, &[elem, pred])
}

fn ex_intro(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    elem: ExprId,
    pred: ExprId,
    w: ExprId,
    proof: ExprId,
) -> ExprId {
    let c = k.const_(lg.exists_intro, vec![l1]);
    t_app(k, c, &[elem, pred, w, proof])
}

/// `Exists.rec elem pred (fun _ => target) minor h`, with the minor premise
/// built by a closure over the witness `w` and its property `hw`.
///
/// `wfv`/`hwfv` are passed in rather than fixed because these eliminations
/// NEST (`closedAdd` on a principal ideal opens two existentials at once),
/// and a shared free variable would let the inner `lam_over` capture the
/// outer witness.
#[allow(clippy::too_many_arguments)]
fn ex_elim(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    elem: ExprId,
    pred: ExprId,
    target: ExprId,
    h: ExprId,
    wfv: u64,
    hwfv: u64,
    build: impl FnOnce(&mut Kernel, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let w = k.fvar(wfv);
    let pred_w = k.app(pred, w);
    let hw = k.fvar(hwfv);
    let body = build(k, w, hw);
    let minor = lam_over(k, hwfv, pred_w, body);
    let minor = lam_over(k, wfv, elem, minor);

    let ex_ty = ex_of(k, lg, l1, elem, pred);
    let motive = lam_over(k, MOT_FV, ex_ty, target);
    let rec = k.const_(lg.exists_rec, vec![l1]);
    t_app(k, rec, &[elem, pred, motive, minor, h])
}

// ---------------------------------------------------------------------------
// The three instances are ideals.
// ---------------------------------------------------------------------------

/// `AlgS.Ideal.bot_isIdeal : forall R, IsIdeal R (AlgS.Ideal.bot R)`.
#[allow(clippy::too_many_arguments)]
fn declare_bot_is_ideal(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    deps: &IdealDeps,
    is_ideal: NameId,
    bot: NameId,
    zero_add: NameId,
    neg_zero: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let bot_r = {
        let t = k.const_(bot, vec![]);
        k.app(t, c.r)
    };
    let props = five_stmts(k, &c, bot_r);

    // 0 respects : `a ~ b -> a ~ 0 -> b ~ 0`.
    let p_respects = {
        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let h1 = k.fvar(H1_FV);
        let h2 = k.fvar(H2_FV);
        let ba = c.sy(k, a, b, h1);
        let body = c.tr(k, b, a, c.zero, ba, h2);
        let hyp1 = c.eqv(k, a, b);
        let hyp2 = c.eqv(k, a, c.zero);
        let v = lam_over(k, H2_FV, hyp2, body);
        let v = lam_over(k, H1_FV, hyp1, v);
        let v = lam_over(k, B_FV, c.carrier, v);
        lam_over(k, A_FV, c.carrier, v)
    };
    // 1 memZero : `0 ~ 0`.
    let p_mem_zero = c.rf(k, c.zero);
    // 2 closedAdd : `a ~ 0 -> b ~ 0 -> a + b ~ 0`.
    let p_closed_add = {
        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let h1 = k.fvar(H1_FV);
        let h2 = k.fvar(H2_FV);
        let ab = c.pl(k, a, b);
        let zz = c.pl(k, c.zero, c.zero);
        let mut ch = Chain::start(k, &c, ab);
        let s1 = c.addc(k, a, c.zero, b, c.zero, h1, h2);
        ch.step(k, &c, zz, s1);
        let s2 = {
            let t = k.const_(zero_add, vec![]);
            t_app(k, t, &[c.r, c.zero])
        };
        ch.step(k, &c, c.zero, s2);
        let hyp1 = c.eqv(k, a, c.zero);
        let hyp2 = c.eqv(k, b, c.zero);
        let v = lam_over(k, H2_FV, hyp2, ch.p);
        let v = lam_over(k, H1_FV, hyp1, v);
        let v = lam_over(k, B_FV, c.carrier, v);
        lam_over(k, A_FV, c.carrier, v)
    };
    // 3 closedNeg : `a ~ 0 -> -a ~ 0`.
    let p_closed_neg = {
        let a = k.fvar(A_FV);
        let h1 = k.fvar(H1_FV);
        let na = c.ng(k, a);
        let nz = c.ng(k, c.zero);
        let mut ch = Chain::start(k, &c, na);
        let s1 = c.negc(k, a, c.zero, h1);
        ch.step(k, &c, nz, s1);
        let s2 = {
            let t = k.const_(neg_zero, vec![]);
            k.app(t, c.r)
        };
        ch.step(k, &c, c.zero, s2);
        let hyp1 = c.eqv(k, a, c.zero);
        let v = lam_over(k, H1_FV, hyp1, ch.p);
        lam_over(k, A_FV, c.carrier, v)
    };
    // 4 absorb : `a ~ 0 -> r * a ~ 0`.
    let p_absorb = {
        let s = k.fvar(X_FV);
        let a = k.fvar(A_FV);
        let h1 = k.fvar(H1_FV);
        let sa = c.tm(k, s, a);
        let s_zero = c.tm(k, s, c.zero);
        let mut ch = Chain::start(k, &c, sa);
        let rs = c.rf(k, s);
        let s1 = c.mulc(k, s, s, a, c.zero, rs, h1);
        ch.step(k, &c, s_zero, s1);
        let mz = at_ring(k, &c, deps, deps.mul_zero);
        let s2 = k.app(mz, s);
        ch.step(k, &c, c.zero, s2);
        let hyp1 = c.eqv(k, a, c.zero);
        let v = lam_over(k, H1_FV, hyp1, ch.p);
        let v = lam_over(k, A_FV, c.carrier, v);
        lam_over(k, X_FV, c.carrier, v)
    };

    let proofs = [p_respects, p_mem_zero, p_closed_add, p_closed_neg, p_absorb];
    let value = intro_and(k, lg, &props, &proofs);
    let value = close_r(k, &c, value, true);
    let ty = is_ideal_at(k, &c, is_ideal, bot_r);
    let ty = close_r(k, &c, ty, false);
    theorem(k, ns, "bot_isIdeal", ty, value)
}

/// `AlgS.Ideal.top_isIdeal : forall R, IsIdeal R (AlgS.Ideal.top R)` — every
/// conjunct is `True.intro` under the right stack of binders.
fn declare_top_is_ideal(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    is_ideal: NameId,
    top: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let top_r = {
        let t = k.const_(top, vec![]);
        k.app(t, c.r)
    };
    let props = five_stmts(k, &c, top_r);
    let ti = k.const_(lg.true_intro, vec![]);
    let true_c = k.const_(lg.true_, vec![]);

    let p_respects = {
        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let hyp1 = c.eqv(k, a, b);
        let v = lam_over(k, H2_FV, true_c, ti);
        let v = lam_over(k, H1_FV, hyp1, v);
        let v = lam_over(k, B_FV, c.carrier, v);
        lam_over(k, A_FV, c.carrier, v)
    };
    let p_mem_zero = ti;
    let p_closed_add = {
        let v = lam_over(k, H2_FV, true_c, ti);
        let v = lam_over(k, H1_FV, true_c, v);
        let v = lam_over(k, B_FV, c.carrier, v);
        lam_over(k, A_FV, c.carrier, v)
    };
    let p_closed_neg = {
        let v = lam_over(k, H1_FV, true_c, ti);
        lam_over(k, A_FV, c.carrier, v)
    };
    let p_absorb = {
        let v = lam_over(k, H1_FV, true_c, ti);
        let v = lam_over(k, A_FV, c.carrier, v);
        lam_over(k, X_FV, c.carrier, v)
    };

    let proofs = [p_respects, p_mem_zero, p_closed_add, p_closed_neg, p_absorb];
    let value = intro_and(k, lg, &props, &proofs);
    let value = close_r(k, &c, value, true);
    let ty = is_ideal_at(k, &c, is_ideal, top_r);
    let ty = close_r(k, &c, ty, false);
    theorem(k, ns, "top_isIdeal", ty, value)
}

/// `AlgS.Ideal.principal_isIdeal : forall R g,
/// IsIdeal R (AlgS.Ideal.principal R g)` — the one that actually exercises
/// `Exists` elimination and every helper lemma above.
#[allow(clippy::too_many_arguments)]
fn declare_principal_is_ideal(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    cr: &RecordNames,
    is_ideal: NameId,
    principal: NameId,
    zero_mul: NameId,
    mul_neg_l: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let g = k.fvar(G_FV);
    let prin = {
        let t = k.const_(principal, vec![]);
        app2(k, t, c.r, g)
    };
    let props = five_stmts(k, &c, prin);

    // `fun r => x ~ r * g` for a given `x`.
    let pred_at = |k: &mut Kernel, c: &RCtx, x: ExprId| -> ExprId {
        let r = k.fvar(W_FV);
        let rg = c.tm(k, r, g);
        let inner = c.eqv(k, x, rg);
        lam_over(k, W_FV, c.carrier, inner)
    };

    // 0 respects.
    let p_respects = {
        let x = k.fvar(X_FV);
        let y = k.fvar(Y_FV);
        let h1 = k.fvar(H1_FV);
        let h2 = k.fvar(H2_FV);
        let pred_x = pred_at(k, &c, x);
        let pred_y = pred_at(k, &c, y);
        let target = ex_of(k, lg, l1, c.carrier, pred_y);
        let body = ex_elim(
            k,
            lg,
            l1,
            c.carrier,
            pred_x,
            target,
            h2,
            W_FV,
            HW_FV,
            |k, w, hw| {
                let wg = c.tm(k, w, g);
                let yx = c.sy(k, x, y, h1);
                let proof = c.tr(k, y, x, wg, yx, hw);
                ex_intro(k, lg, l1, c.carrier, pred_y, w, proof)
            },
        );
        let hyp1 = c.eqv(k, x, y);
        let hyp2 = ex_of(k, lg, l1, c.carrier, pred_x);
        let v = lam_over(k, H2_FV, hyp2, body);
        let v = lam_over(k, H1_FV, hyp1, v);
        let v = lam_over(k, Y_FV, c.carrier, v);
        lam_over(k, X_FV, c.carrier, v)
    };

    // 1 memZero : witness `0`, since `0 ~ 0 * g`.
    let p_mem_zero = {
        let pred_z = pred_at(k, &c, c.zero);
        let zg = c.tm(k, c.zero, g);
        let zm = {
            let t = k.const_(zero_mul, vec![]);
            t_app(k, t, &[c.r, g])
        };
        let proof = c.sy(k, zg, c.zero, zm);
        ex_intro(k, lg, l1, c.carrier, pred_z, c.zero, proof)
    };

    // 2 closedAdd : witness `w1 + w2`.
    let p_closed_add = {
        let x = k.fvar(X_FV);
        let y = k.fvar(Y_FV);
        let h1 = k.fvar(H1_FV);
        let h2 = k.fvar(H2_FV);
        let pred_x = pred_at(k, &c, x);
        let pred_y = pred_at(k, &c, y);
        let xy = c.pl(k, x, y);
        let pred_xy = pred_at(k, &c, xy);
        let target = ex_of(k, lg, l1, c.carrier, pred_xy);
        let inner_target = target;
        let body = ex_elim(
            k,
            lg,
            l1,
            c.carrier,
            pred_x,
            target,
            h1,
            W_FV,
            HW_FV,
            |k, w1, hw1| {
                ex_elim(
                    k,
                    lg,
                    l1,
                    c.carrier,
                    pred_y,
                    inner_target,
                    h2,
                    W2_FV,
                    HW2_FV,
                    |k, w2, hw2| {
                        let w1g = c.tm(k, w1, g);
                        let w2g = c.tm(k, w2, g);
                        let sum = c.pl(k, w1g, w2g);
                        let w12 = c.pl(k, w1, w2);
                        let w12g = c.tm(k, w12, g);
                        let mut ch = Chain::start(k, &c, xy);
                        let s1 = c.addc(k, x, w1g, y, w2g, hw1, hw2);
                        ch.step(k, &c, sum, s1);
                        let dr = t_app(k, c.distrib_r, &[w1, w2, g]);
                        let s2 = c.sy(k, w12g, sum, dr);
                        ch.step(k, &c, w12g, s2);
                        ex_intro(k, lg, l1, c.carrier, pred_xy, w12, ch.p)
                    },
                )
            },
        );
        let hyp1 = ex_of(k, lg, l1, c.carrier, pred_x);
        let hyp2 = ex_of(k, lg, l1, c.carrier, pred_y);
        let v = lam_over(k, H2_FV, hyp2, body);
        let v = lam_over(k, H1_FV, hyp1, v);
        let v = lam_over(k, Y_FV, c.carrier, v);
        lam_over(k, X_FV, c.carrier, v)
    };

    // 3 closedNeg : witness `-w`.
    let p_closed_neg = {
        let x = k.fvar(X_FV);
        let h1 = k.fvar(H1_FV);
        let pred_x = pred_at(k, &c, x);
        let nx = c.ng(k, x);
        let pred_nx = pred_at(k, &c, nx);
        let target = ex_of(k, lg, l1, c.carrier, pred_nx);
        let body = ex_elim(
            k,
            lg,
            l1,
            c.carrier,
            pred_x,
            target,
            h1,
            W_FV,
            HW_FV,
            |k, w, hw| {
                let wg = c.tm(k, w, g);
                let nwg = c.ng(k, wg);
                let nw = c.ng(k, w);
                let nw_g = c.tm(k, nw, g);
                let mut ch = Chain::start(k, &c, nx);
                let s1 = c.negc(k, x, wg, hw);
                ch.step(k, &c, nwg, s1);
                let mnl = {
                    let t = k.const_(mul_neg_l, vec![]);
                    t_app(k, t, &[c.r, w, g])
                };
                let s2 = c.sy(k, nw_g, nwg, mnl);
                ch.step(k, &c, nw_g, s2);
                ex_intro(k, lg, l1, c.carrier, pred_nx, nw, ch.p)
            },
        );
        let hyp1 = ex_of(k, lg, l1, c.carrier, pred_x);
        let v = lam_over(k, H1_FV, hyp1, body);
        lam_over(k, X_FV, c.carrier, v)
    };

    // 4 absorb : witness `s * w`.
    let p_absorb = {
        let s = k.fvar(Z_FV);
        let x = k.fvar(X_FV);
        let h1 = k.fvar(H1_FV);
        let pred_x = pred_at(k, &c, x);
        let sx = c.tm(k, s, x);
        let pred_sx = pred_at(k, &c, sx);
        let target = ex_of(k, lg, l1, c.carrier, pred_sx);
        let body = ex_elim(
            k,
            lg,
            l1,
            c.carrier,
            pred_x,
            target,
            h1,
            W_FV,
            HW_FV,
            |k, w, hw| {
                let wg = c.tm(k, w, g);
                let s_wg = c.tm(k, s, wg);
                let sw = c.tm(k, s, w);
                let sw_g = c.tm(k, sw, g);
                let mut ch = Chain::start(k, &c, sx);
                let rs = c.rf(k, s);
                let s1 = c.mulc(k, s, s, x, wg, rs, hw);
                ch.step(k, &c, s_wg, s1);
                let ma = t_app(k, c.mul_assoc, &[s, w, g]);
                let s2 = c.sy(k, sw_g, s_wg, ma);
                ch.step(k, &c, sw_g, s2);
                ex_intro(k, lg, l1, c.carrier, pred_sx, sw, ch.p)
            },
        );
        let hyp1 = ex_of(k, lg, l1, c.carrier, pred_x);
        let v = lam_over(k, H1_FV, hyp1, body);
        let v = lam_over(k, X_FV, c.carrier, v);
        lam_over(k, Z_FV, c.carrier, v)
    };

    let proofs = [p_respects, p_mem_zero, p_closed_add, p_closed_neg, p_absorb];
    let value = intro_and(k, lg, &props, &proofs);
    let value = lam_over(k, G_FV, c.carrier, value);
    let value = close_r(k, &c, value, true);
    let ty = is_ideal_at(k, &c, is_ideal, prin);
    let ty = pi_over(k, G_FV, c.carrier, ty);
    let ty = close_r(k, &c, ty, false);
    theorem(k, ns, "principal_isIdeal", ty, value)
}

// ---------------------------------------------------------------------------
// `R/I` — the coset relation, the one lemma that makes every ring LAW free,
// and the six congruence obligations a real `Quot` would discharge for us.
// ---------------------------------------------------------------------------

/// `I (R.add x (R.neg y))` — the coset relation, spelled out. Every
/// statement below uses this RAW form rather than the `quotEquiv` constant,
/// so that matching it against a record field's expected type costs beta
/// only, never a delta unfold.
fn qrel(k: &mut Kernel, c: &RCtx, i: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let ny = c.ng(k, y);
    let diff = c.pl(k, x, ny);
    k.app(i, diff)
}

/// `AlgS.Ideal.quotEquiv : forall R (I : R.carrier -> Prop),
/// R.carrier -> R.carrier -> Prop := fun R I x y => I (R.add x (R.neg y))`
/// — the named form of the coset relation, for readers and for
/// `quotient_equiv`.
fn declare_quot_equiv(k: &mut Kernel, cr: &RecordNames, ns: NameId) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let x = k.fvar(X_FV);
    let y = k.fvar(Y_FV);
    let body = qrel(k, &c, i, x, y);
    let body = lam_over(k, Y_FV, c.carrier, body);
    let body = lam_over(k, X_FV, c.carrier, body);
    let value = close_ri(k, &c, body, true);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = arrow(k, c.carrier, prop);
    let ty = arrow(k, c.carrier, ty);
    let ty = close_ri(k, &c, ty, false);
    definition(k, ns, "quotEquiv", ty, value)
}

/// `AlgS.Ideal.ofEquiv : forall R I (hI : IsIdeal R I) x y,
/// R.equiv x y -> I (R.add x (R.neg y))`.
///
/// **This is why the quotient's ten ring-law fields are free.** The coset
/// relation is COARSER than `R.equiv`, so every law `R` already proves
/// transports to `R/I` through this one four-step lemma, and no ring law is
/// re-proved.
fn declare_of_equiv(
    k: &mut Kernel,
    cr: &RecordNames,
    is_ideal: NameId,
    acc: AccNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let hi_ty = is_ideal_at(k, &c, is_ideal, i);
    let hi = k.fvar(HI_FV);
    let x = k.fvar(X_FV);
    let y = k.fvar(Y_FV);
    let h = k.fvar(H1_FV);

    let ny = c.ng(k, y);
    let diff = c.pl(k, x, ny);
    let yny = c.pl(k, y, ny);

    let mut ch = Chain::start(k, &c, diff);
    let rny = c.rf(k, ny);
    let s1 = c.addc(k, x, y, ny, ny, h, rny);
    ch.step(k, &c, yny, s1);
    let s2 = k.app(c.neg_add, y);
    ch.step(k, &c, c.zero, s2);
    let back = c.sy(k, diff, c.zero, ch.p);

    let respects = acc_at(k, &c, acc.respects, i, hi);
    let mem_zero = acc_at(k, &c, acc.mem_zero, i, hi);
    let body = t_app(k, respects, &[c.zero, diff, back, mem_zero]);

    let hyp = c.eqv(k, x, y);
    let value = lam_over(k, H1_FV, hyp, body);
    let value = lam_over(k, Y_FV, c.carrier, value);
    let value = lam_over(k, X_FV, c.carrier, value);
    let value = close_rih(k, &c, hi_ty, value, true);

    let concl = k.app(i, diff);
    let ty = pi_over(k, H1_FV, hyp, concl);
    let ty = pi_over(k, Y_FV, c.carrier, ty);
    let ty = pi_over(k, X_FV, c.carrier, ty);
    let ty = close_rih(k, &c, hi_ty, ty, false);
    theorem(k, ns, "ofEquiv", ty, value)
}

/// **Quotient obligation 1 of 6**: `AlgS.Ideal.quotRefl : forall R I hI x,
/// I (x + (-x))` — the quotient's `equivRefl` field.
fn declare_quot_refl(
    k: &mut Kernel,
    cr: &RecordNames,
    is_ideal: NameId,
    of_equiv: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let hi_ty = is_ideal_at(k, &c, is_ideal, i);
    let hi = k.fvar(HI_FV);
    let x = k.fvar(X_FV);

    let oe = {
        let t = k.const_(of_equiv, vec![]);
        t_app(k, t, &[c.r, i, hi])
    };
    let rx = c.rf(k, x);
    let body = t_app(k, oe, &[x, x, rx]);

    let value = lam_over(k, X_FV, c.carrier, body);
    let value = close_rih(k, &c, hi_ty, value, true);

    let concl = qrel(k, &c, i, x, x);
    let ty = pi_over(k, X_FV, c.carrier, concl);
    let ty = close_rih(k, &c, hi_ty, ty, false);
    theorem(k, ns, "quotRefl", ty, value)
}

/// **Quotient obligation 2 of 6**: `AlgS.Ideal.quotSymm : forall R I hI x y,
/// I (x + (-y)) -> I (y + (-x))` — the quotient's `equivSymm` field, and the
/// only place `closedNeg` is load-bearing on its own.
#[allow(clippy::too_many_arguments)]
fn declare_quot_symm(
    k: &mut Kernel,
    cr: &RecordNames,
    deps: &IdealDeps,
    is_ideal: NameId,
    acc: AccNames,
    neg_add_dist: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let hi_ty = is_ideal_at(k, &c, is_ideal, i);
    let hi = k.fvar(HI_FV);
    let x = k.fvar(X_FV);
    let y = k.fvar(Y_FV);
    let h = k.fvar(H1_FV);

    let ny = c.ng(k, y);
    let nx = c.ng(k, x);
    let diff = c.pl(k, x, ny);
    let ndiff = c.ng(k, diff);
    let nny = c.ng(k, ny);
    let mid = c.pl(k, nx, nny);
    let mid2 = c.pl(k, nx, y);
    let goal = c.pl(k, y, nx);

    let mut ch = Chain::start(k, &c, ndiff);
    let nad = {
        let t = k.const_(neg_add_dist, vec![]);
        t_app(k, t, &[c.r, x, ny])
    };
    ch.step(k, &c, mid, nad);
    let nn = at_ring(k, &c, deps, deps.neg_neg);
    let nn_y = k.app(nn, y);
    let rnx = c.rf(k, nx);
    let s2 = c.addc(k, nx, nx, nny, y, rnx, nn_y);
    ch.step(k, &c, mid2, s2);
    let s3 = t_app(k, c.add_comm, &[nx, y]);
    ch.step(k, &c, goal, s3);

    let closed_neg = acc_at(k, &c, acc.closed_neg, i, hi);
    let neg_h = t_app(k, closed_neg, &[diff, h]);
    let respects = acc_at(k, &c, acc.respects, i, hi);
    let body = t_app(k, respects, &[ndiff, goal, ch.p, neg_h]);

    let hyp = k.app(i, diff);
    let value = lam_over(k, H1_FV, hyp, body);
    let value = lam_over(k, Y_FV, c.carrier, value);
    let value = lam_over(k, X_FV, c.carrier, value);
    let value = close_rih(k, &c, hi_ty, value, true);

    let concl = k.app(i, goal);
    let ty = pi_over(k, H1_FV, hyp, concl);
    let ty = pi_over(k, Y_FV, c.carrier, ty);
    let ty = pi_over(k, X_FV, c.carrier, ty);
    let ty = close_rih(k, &c, hi_ty, ty, false);
    theorem(k, ns, "quotSymm", ty, value)
}

/// **Quotient obligation 3 of 6**: `AlgS.Ideal.quotTrans : forall R I hI
/// x y z, I (x + (-y)) -> I (y + (-z)) -> I (x + (-z))`.
#[allow(clippy::too_many_arguments)]
fn declare_quot_trans(
    k: &mut Kernel,
    cr: &RecordNames,
    is_ideal: NameId,
    acc: AccNames,
    add_regroup: NameId,
    neg_add_l: NameId,
    zero_add: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let hi_ty = is_ideal_at(k, &c, is_ideal, i);
    let hi = k.fvar(HI_FV);
    let x = k.fvar(X_FV);
    let y = k.fvar(Y_FV);
    let z = k.fvar(Z_FV);
    let h1 = k.fvar(H1_FV);
    let h2 = k.fvar(H2_FV);

    let ny = c.ng(k, y);
    let nz = c.ng(k, z);
    let d1 = c.pl(k, x, ny);
    let d2 = c.pl(k, y, nz);
    let sum = c.pl(k, d1, d2);
    let nyy = c.pl(k, ny, y);
    let nyy_nz = c.pl(k, nyy, nz);
    let regrouped = c.pl(k, x, nyy_nz);
    let zero_nz = c.pl(k, c.zero, nz);
    let goal = c.pl(k, x, nz);

    // inner : `((-y) + y) + (-z) ~ (-z)`
    let inner = {
        let mut ic = Chain::start(k, &c, nyy_nz);
        let nal = {
            let t = k.const_(neg_add_l, vec![]);
            t_app(k, t, &[c.r, y])
        };
        let rnz = c.rf(k, nz);
        let i1 = c.addc(k, nyy, c.zero, nz, nz, nal, rnz);
        ic.step(k, &c, zero_nz, i1);
        let za = {
            let t = k.const_(zero_add, vec![]);
            t_app(k, t, &[c.r, nz])
        };
        ic.step(k, &c, nz, za);
        ic.p
    };

    let mut ch = Chain::start(k, &c, sum);
    let ar = {
        let t = k.const_(add_regroup, vec![]);
        t_app(k, t, &[c.r, x, ny, y, nz])
    };
    ch.step(k, &c, regrouped, ar);
    let rx = c.rf(k, x);
    let s2 = c.addc(k, x, x, nyy_nz, nz, rx, inner);
    ch.step(k, &c, goal, s2);

    let closed_add = acc_at(k, &c, acc.closed_add, i, hi);
    let sum_h = t_app(k, closed_add, &[d1, d2, h1, h2]);
    let respects = acc_at(k, &c, acc.respects, i, hi);
    let body = t_app(k, respects, &[sum, goal, ch.p, sum_h]);

    let hyp1 = k.app(i, d1);
    let hyp2 = k.app(i, d2);
    let value = lam_over(k, H2_FV, hyp2, body);
    let value = lam_over(k, H1_FV, hyp1, value);
    let value = lam_over(k, Z_FV, c.carrier, value);
    let value = lam_over(k, Y_FV, c.carrier, value);
    let value = lam_over(k, X_FV, c.carrier, value);
    let value = close_rih(k, &c, hi_ty, value, true);

    let concl = k.app(i, goal);
    let ty = pi_over(k, H2_FV, hyp2, concl);
    let ty = pi_over(k, H1_FV, hyp1, ty);
    let ty = pi_over(k, Z_FV, c.carrier, ty);
    let ty = pi_over(k, Y_FV, c.carrier, ty);
    let ty = pi_over(k, X_FV, c.carrier, ty);
    let ty = close_rih(k, &c, hi_ty, ty, false);
    theorem(k, ns, "quotTrans", ty, value)
}

/// **Quotient obligation 4 of 6**: `AlgS.Ideal.quotAddCongr : forall R I hI
/// a a' b b', I (a + (-a')) -> I (b + (-b')) ->
/// I ((a + b) + (-(a' + b')))` — the quotient's `addCongr` field.
#[allow(clippy::too_many_arguments)]
fn declare_quot_add_congr(
    k: &mut Kernel,
    cr: &RecordNames,
    is_ideal: NameId,
    acc: AccNames,
    add_swap_mid: NameId,
    neg_add_dist: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let hi_ty = is_ideal_at(k, &c, is_ideal, i);
    let hi = k.fvar(HI_FV);
    let a = k.fvar(A_FV);
    let ap = k.fvar(AP_FV);
    let b = k.fvar(B_FV);
    let bp = k.fvar(BP_FV);
    let h1 = k.fvar(H1_FV);
    let h2 = k.fvar(H2_FV);

    let nap = c.ng(k, ap);
    let nbp = c.ng(k, bp);
    let d1 = c.pl(k, a, nap);
    let d2 = c.pl(k, b, nbp);
    let sum = c.pl(k, d1, d2);
    let ab = c.pl(k, a, b);
    let napnbp = c.pl(k, nap, nbp);
    let swapped = c.pl(k, ab, napnbp);
    let apbp = c.pl(k, ap, bp);
    let napbp = c.ng(k, apbp);
    let goal = c.pl(k, ab, napbp);

    let mut ch = Chain::start(k, &c, sum);
    let asm = {
        let t = k.const_(add_swap_mid, vec![]);
        t_app(k, t, &[c.r, a, nap, b, nbp])
    };
    ch.step(k, &c, swapped, asm);
    let nad = {
        let t = k.const_(neg_add_dist, vec![]);
        t_app(k, t, &[c.r, ap, bp])
    };
    let nad_back = c.sy(k, napbp, napnbp, nad);
    let rab = c.rf(k, ab);
    let s2 = c.addc(k, ab, ab, napnbp, napbp, rab, nad_back);
    ch.step(k, &c, goal, s2);

    let closed_add = acc_at(k, &c, acc.closed_add, i, hi);
    let sum_h = t_app(k, closed_add, &[d1, d2, h1, h2]);
    let respects = acc_at(k, &c, acc.respects, i, hi);
    let body = t_app(k, respects, &[sum, goal, ch.p, sum_h]);

    let hyp1 = k.app(i, d1);
    let hyp2 = k.app(i, d2);
    let value = lam_over(k, H2_FV, hyp2, body);
    let value = lam_over(k, H1_FV, hyp1, value);
    let value = lam_over(k, BP_FV, c.carrier, value);
    let value = lam_over(k, B_FV, c.carrier, value);
    let value = lam_over(k, AP_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = close_rih(k, &c, hi_ty, value, true);

    let concl = k.app(i, goal);
    let ty = pi_over(k, H2_FV, hyp2, concl);
    let ty = pi_over(k, H1_FV, hyp1, ty);
    let ty = pi_over(k, BP_FV, c.carrier, ty);
    let ty = pi_over(k, B_FV, c.carrier, ty);
    let ty = pi_over(k, AP_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = close_rih(k, &c, hi_ty, ty, false);
    theorem(k, ns, "quotAddCongr", ty, value)
}

/// **Quotient obligation 5 of 6**: `AlgS.Ideal.quotNegCongr : forall R I hI
/// a a', I (a + (-a')) -> I ((-a) + (-(-a')))`.
fn declare_quot_neg_congr(
    k: &mut Kernel,
    cr: &RecordNames,
    is_ideal: NameId,
    acc: AccNames,
    neg_add_dist: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let hi_ty = is_ideal_at(k, &c, is_ideal, i);
    let hi = k.fvar(HI_FV);
    let a = k.fvar(A_FV);
    let ap = k.fvar(AP_FV);
    let h = k.fvar(H1_FV);

    let nap = c.ng(k, ap);
    let d1 = c.pl(k, a, nap);
    let nd1 = c.ng(k, d1);
    let na = c.ng(k, a);
    let nnap = c.ng(k, nap);
    let goal = c.pl(k, na, nnap);

    let nad = {
        let t = k.const_(neg_add_dist, vec![]);
        t_app(k, t, &[c.r, a, nap])
    };
    let closed_neg = acc_at(k, &c, acc.closed_neg, i, hi);
    let neg_h = t_app(k, closed_neg, &[d1, h]);
    let respects = acc_at(k, &c, acc.respects, i, hi);
    let body = t_app(k, respects, &[nd1, goal, nad, neg_h]);

    let hyp = k.app(i, d1);
    let value = lam_over(k, H1_FV, hyp, body);
    let value = lam_over(k, AP_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = close_rih(k, &c, hi_ty, value, true);

    let concl = k.app(i, goal);
    let ty = pi_over(k, H1_FV, hyp, concl);
    let ty = pi_over(k, AP_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = close_rih(k, &c, hi_ty, ty, false);
    theorem(k, ns, "quotNegCongr", ty, value)
}

/// **Quotient obligation 6 of 6, and the one the absorbing law exists for**:
/// `AlgS.Ideal.quotMulCongr : forall R I hI a a' b b',
/// I (a + (-a')) -> I (b + (-b')) -> I ((a * b) + (-(a' * b')))`.
///
/// The identity behind it is `a*b - a'*b' = a*(b - b') + b'*(a - a')`, and
/// **both** summands are in `I` only because `absorb` lets an arbitrary ring
/// element multiply a member. Drop `absorb` from `IsIdeal` and this is the
/// obligation that becomes unprovable.
#[allow(clippy::too_many_arguments)]
fn declare_quot_mul_congr(
    k: &mut Kernel,
    cr: &RecordNames,
    is_ideal: NameId,
    acc: AccNames,
    add_regroup: NameId,
    neg_add_l: NameId,
    zero_add: NameId,
    mul_neg_r: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let hi_ty = is_ideal_at(k, &c, is_ideal, i);
    let hi = k.fvar(HI_FV);
    let a = k.fvar(A_FV);
    let ap = k.fvar(AP_FV);
    let b = k.fvar(B_FV);
    let bp = k.fvar(BP_FV);
    let h1 = k.fvar(H1_FV);
    let h2 = k.fvar(H2_FV);

    let nap = c.ng(k, ap);
    let nbp = c.ng(k, bp);
    let d1 = c.pl(k, a, nap); // a - a'
    let d2 = c.pl(k, b, nbp); // b - b'
    let a_d2 = c.tm(k, a, d2); // a * (b - b')
    let bp_d1 = c.tm(k, bp, d1); // b' * (a - a')
    let sum = c.pl(k, a_d2, bp_d1);

    let ab = c.tm(k, a, b);
    let a_nbp = c.tm(k, a, nbp);
    let bp_a = c.tm(k, bp, a);
    let bp_nap = c.tm(k, bp, nap);
    let left = c.pl(k, ab, a_nbp);
    let right = c.pl(k, bp_a, bp_nap);
    let expanded = c.pl(k, left, right);

    let u_v = c.pl(k, a_nbp, bp_a);
    let uv_w = c.pl(k, u_v, bp_nap);
    let regrouped = c.pl(k, ab, uv_w);

    let abp = c.tm(k, a, bp);
    let nabp = c.ng(k, abp);
    let cancel_pair = c.pl(k, nabp, abp);
    let zero_w = c.pl(k, c.zero, bp_nap);
    let bpap = c.tm(k, bp, ap);
    let nbpap = c.ng(k, bpap);
    let apbp = c.tm(k, ap, bp);
    let napbp = c.ng(k, apbp);
    let goal = c.pl(k, ab, napbp);

    // 1. distribute both products.
    let mut ch = Chain::start(k, &c, sum);
    let dl1 = t_app(k, c.distrib_l, &[a, b, nbp]);
    let dl2 = t_app(k, c.distrib_l, &[bp, a, nap]);
    let s1 = c.addc(k, a_d2, left, bp_d1, right, dl1, dl2);
    ch.step(k, &c, expanded, s1);

    // 2. regroup so the cancelling pair `a*(-b') + b'*a` sits together.
    let ar = {
        let t = k.const_(add_regroup, vec![]);
        t_app(k, t, &[c.r, ab, a_nbp, bp_a, bp_nap])
    };
    ch.step(k, &c, regrouped, ar);

    // 3. `(a*(-b') + b'*a) + b'*(-a') ~ -(a'*b')`.
    let inner = {
        // `a*(-b') + b'*a ~ 0`
        let cancel = {
            let mut cc = Chain::start(k, &c, u_v);
            let mnr = {
                let t = k.const_(mul_neg_r, vec![]);
                t_app(k, t, &[c.r, a, bp])
            };
            let comm = t_app(k, c.mul_comm, &[bp, a]);
            let c1 = c.addc(k, a_nbp, nabp, bp_a, abp, mnr, comm);
            cc.step(k, &c, cancel_pair, c1);
            let nal = {
                let t = k.const_(neg_add_l, vec![]);
                t_app(k, t, &[c.r, abp])
            };
            cc.step(k, &c, c.zero, nal);
            cc.p
        };
        let mut ic = Chain::start(k, &c, uv_w);
        let rw = c.rf(k, bp_nap);
        let i1 = c.addc(k, u_v, c.zero, bp_nap, bp_nap, cancel, rw);
        ic.step(k, &c, zero_w, i1);
        let za = {
            let t = k.const_(zero_add, vec![]);
            t_app(k, t, &[c.r, bp_nap])
        };
        ic.step(k, &c, bp_nap, za);
        // `b'*(-a') ~ -(b'*a') ~ -(a'*b')`
        let mnr2 = {
            let t = k.const_(mul_neg_r, vec![]);
            t_app(k, t, &[c.r, bp, ap])
        };
        ic.step(k, &c, nbpap, mnr2);
        let comm2 = t_app(k, c.mul_comm, &[bp, ap]);
        let i3 = c.negc(k, bpap, apbp, comm2);
        ic.step(k, &c, napbp, i3);
        ic.p
    };
    let rab = c.rf(k, ab);
    let s3 = c.addc(k, ab, ab, uv_w, napbp, rab, inner);
    ch.step(k, &c, goal, s3);

    // The two `absorb` applications, then `closedAdd`.
    let absorb = acc_at(k, &c, acc.absorb, i, hi);
    let u = t_app(k, absorb, &[a, d2, h2]);
    let v = t_app(k, absorb, &[bp, d1, h1]);
    let closed_add = acc_at(k, &c, acc.closed_add, i, hi);
    let sum_h = t_app(k, closed_add, &[a_d2, bp_d1, u, v]);
    let respects = acc_at(k, &c, acc.respects, i, hi);
    let body = t_app(k, respects, &[sum, goal, ch.p, sum_h]);

    let hyp1 = k.app(i, d1);
    let hyp2 = k.app(i, d2);
    let value = lam_over(k, H2_FV, hyp2, body);
    let value = lam_over(k, H1_FV, hyp1, value);
    let value = lam_over(k, BP_FV, c.carrier, value);
    let value = lam_over(k, B_FV, c.carrier, value);
    let value = lam_over(k, AP_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = close_rih(k, &c, hi_ty, value, true);

    let concl = k.app(i, goal);
    let ty = pi_over(k, H2_FV, hyp2, concl);
    let ty = pi_over(k, H1_FV, hyp1, ty);
    let ty = pi_over(k, BP_FV, c.carrier, ty);
    let ty = pi_over(k, B_FV, c.carrier, ty);
    let ty = pi_over(k, AP_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = close_rih(k, &c, hi_ty, ty, false);
    theorem(k, ns, "quotMulCongr", ty, value)
}

/// Names of the six quotient obligations, for [`declare_quotient`].
#[derive(Debug, Clone, Copy)]
struct QuotNames {
    of_equiv: NameId,
    refl: NameId,
    symm: NameId,
    trans: NameId,
    add_congr: NameId,
    neg_congr: NameId,
    mul_congr: NameId,
}

/// `AlgS.Ideal.quotient : forall R I (hI : IsIdeal R I), AlgS.CommRing` —
/// **the quotient ring `R/I`, with no `Quot` anywhere.** All 23 fields are
/// listed in the body so the per-field cost of the setoid route is readable
/// off the source (see the module header for the tally).
fn declare_quotient(
    k: &mut Kernel,
    cr: &RecordNames,
    is_ideal: NameId,
    q: QuotNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let hi_ty = is_ideal_at(k, &c, is_ideal, i);
    let hi = k.fvar(HI_FV);
    let three = [c.r, i, hi];

    let at3 = |k: &mut Kernel, n: NameId| -> ExprId {
        let t = k.const_(n, vec![]);
        t_app(k, t, &three)
    };

    // 1 equiv := fun x y => I (x + (-y))
    let equiv_val = {
        let x = k.fvar(X_FV);
        let y = k.fvar(Y_FV);
        let body = qrel(k, &c, i, x, y);
        let t = lam_over(k, Y_FV, c.carrier, body);
        lam_over(k, X_FV, c.carrier, t)
    };

    let refl_val = at3(k, q.refl);
    let symm_val = at3(k, q.symm);
    let trans_val = at3(k, q.trans);
    let add_congr_val = at3(k, q.add_congr);
    let mul_congr_val = at3(k, q.mul_congr);
    let neg_congr_val = at3(k, q.neg_congr);
    let oe = at3(k, q.of_equiv);

    // Every LAW field is `R`'s own law pushed through `ofEquiv`.
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let cv = k.fvar(C_FV);

    let law1 = |k: &mut Kernel, lhs: ExprId, rhs: ExprId, proof: ExprId| -> ExprId {
        let body = t_app(k, oe, &[lhs, rhs, proof]);
        lam_over(k, A_FV, c.carrier, body)
    };
    let law2 = |k: &mut Kernel, lhs: ExprId, rhs: ExprId, proof: ExprId| -> ExprId {
        let body = t_app(k, oe, &[lhs, rhs, proof]);
        let t = lam_over(k, B_FV, c.carrier, body);
        lam_over(k, A_FV, c.carrier, t)
    };
    let law3 = |k: &mut Kernel, lhs: ExprId, rhs: ExprId, proof: ExprId| -> ExprId {
        let body = t_app(k, oe, &[lhs, rhs, proof]);
        let t = lam_over(k, C_FV, c.carrier, body);
        let t = lam_over(k, B_FV, c.carrier, t);
        lam_over(k, A_FV, c.carrier, t)
    };

    let add_assoc_val = {
        let ab = c.pl(k, a, b);
        let lhs = c.pl(k, ab, cv);
        let bc = c.pl(k, b, cv);
        let rhs = c.pl(k, a, bc);
        let p = t_app(k, c.add_assoc, &[a, b, cv]);
        law3(k, lhs, rhs, p)
    };
    let add_comm_val = {
        let lhs = c.pl(k, a, b);
        let rhs = c.pl(k, b, a);
        let p = t_app(k, c.add_comm, &[a, b]);
        law2(k, lhs, rhs, p)
    };
    let add_zero_val = {
        let lhs = c.pl(k, a, c.zero);
        let p = k.app(c.add_zero, a);
        law1(k, lhs, a, p)
    };
    let mul_assoc_val = {
        let ab = c.tm(k, a, b);
        let lhs = c.tm(k, ab, cv);
        let bc = c.tm(k, b, cv);
        let rhs = c.tm(k, a, bc);
        let p = t_app(k, c.mul_assoc, &[a, b, cv]);
        law3(k, lhs, rhs, p)
    };
    let mul_one_l_val = {
        let lhs = c.tm(k, c.one, a);
        let p = k.app(c.mul_one_l, a);
        law1(k, lhs, a, p)
    };
    let mul_one_r_val = {
        let lhs = c.tm(k, a, c.one);
        let p = k.app(c.mul_one_r, a);
        law1(k, lhs, a, p)
    };
    let distrib_l_val = {
        let bc = c.pl(k, b, cv);
        let lhs = c.tm(k, a, bc);
        let ab = c.tm(k, a, b);
        let ac = c.tm(k, a, cv);
        let rhs = c.pl(k, ab, ac);
        let p = t_app(k, c.distrib_l, &[a, b, cv]);
        law3(k, lhs, rhs, p)
    };
    let distrib_r_val = {
        let ab = c.pl(k, a, b);
        let lhs = c.tm(k, ab, cv);
        let ac = c.tm(k, a, cv);
        let bc = c.tm(k, b, cv);
        let rhs = c.pl(k, ac, bc);
        let p = t_app(k, c.distrib_r, &[a, b, cv]);
        law3(k, lhs, rhs, p)
    };
    let neg_add_val = {
        let na = c.ng(k, a);
        let lhs = c.pl(k, a, na);
        let p = k.app(c.neg_add, a);
        law1(k, lhs, c.zero, p)
    };
    let mul_comm_val = {
        let lhs = c.tm(k, a, b);
        let rhs = c.tm(k, b, a);
        let p = t_app(k, c.mul_comm, &[a, b]);
        law2(k, lhs, rhs, p)
    };

    let args = [
        c.carrier,     // 0  carrier   — R's own
        equiv_val,     // 1  equiv     — the coset relation
        refl_val,      // 2  equivRefl     <- proved
        symm_val,      // 3  equivSymm     <- proved
        trans_val,     // 4  equivTrans    <- proved
        c.zero,        // 5  zero      — R's own
        c.one,         // 6  one       — R's own
        c.add,         // 7  add       — R's own
        c.mul,         // 8  mul       — R's own
        add_congr_val, // 9  addCongr      <- proved
        mul_congr_val, // 10 mulCongr      <- proved (needs `absorb`)
        add_assoc_val, // 11 addAssoc      — free via ofEquiv
        add_comm_val,  // 12 addComm       — free
        add_zero_val,  // 13 addZero       — free
        mul_assoc_val, // 14 mulAssoc      — free
        mul_one_l_val, // 15 mulOneL       — free
        mul_one_r_val, // 16 mulOneR       — free
        distrib_l_val, // 17 distribL      — free
        distrib_r_val, // 18 distribR      — free
        c.neg,         // 19 neg       — R's own
        neg_congr_val, // 20 negCongr      <- proved
        neg_add_val,   // 21 negAdd        — free
        mul_comm_val,  // 22 mulComm       — free
    ];
    let value = structures::mk_instance(k, cr, &args);
    let value = close_rih(k, &c, hi_ty, value, true);
    let ty = close_rih(k, &c, hi_ty, c.ring_ty, false);
    definition(k, ns, "quotient", ty, value)
}

/// `AlgS.Ideal.quotient_equiv : forall R I hI x y,
/// Iff (AlgS.CommRing.equiv (quotient R I hI) x y) (quotEquiv R I x y)` —
/// proved by `Iff.intro (fun h => h) (fun h => h)`, so it PASSES only if the
/// record selector on the quotient instance reduces definitionally. A
/// deliberate test, not a convenience lemma.
fn declare_quotient_equiv(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    is_ideal: NameId,
    quotient: NameId,
    quot_equiv: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use idx::comm_ring::EQUIV;
    let c = rctx(k, cr);
    let i = k.fvar(I_FV);
    let hi_ty = is_ideal_at(k, &c, is_ideal, i);
    let hi = k.fvar(HI_FV);
    let three = [c.r, i, hi];

    let quot = {
        let t = k.const_(quotient, vec![]);
        t_app(k, t, &three)
    };
    let q_equiv = sel(k, cr, EQUIV, quot);
    let x = k.fvar(X_FV);
    let y = k.fvar(Y_FV);
    let lhs = app2(k, q_equiv, x, y);
    let rhs = {
        let t = k.const_(quot_equiv, vec![]);
        let t = app2(k, t, c.r, i);
        app2(k, t, x, y)
    };

    let h1 = k.fvar(H1_FV);
    let mp = lam_over(k, H1_FV, lhs, h1);
    let h2 = k.fvar(H2_FV);
    let mpr = lam_over(k, H2_FV, rhs, h2);
    let intro = k.const_(lg.iff_intro, vec![]);
    let body = t_app(k, intro, &[lhs, rhs, mp, mpr]);
    let value = lam_over(k, Y_FV, c.carrier, body);
    let value = lam_over(k, X_FV, c.carrier, value);
    let value = close_rih(k, &c, hi_ty, value, true);

    let iff_c = k.const_(lg.iff, vec![]);
    let concl = app2(k, iff_c, lhs, rhs);
    let ty = pi_over(k, Y_FV, c.carrier, concl);
    let ty = pi_over(k, X_FV, c.carrier, ty);
    let ty = close_rih(k, &c, hi_ty, ty, false);
    theorem(k, ns, "quotient_equiv", ty, value)
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

/// Every name `AlgS.Ideal.*` introduces, in declaration order.
///
/// `#[allow(dead_code)]` for the reason `FieldNames` carries it: these names
/// are deliberately NOT threaded into `NatPrelude` (see the wiring comment in
/// `nat_prelude.rs`), so a consumer re-derives them from the interned `AlgS`
/// root -- which dead-code analysis cannot see. The walking helpers below are
/// `#[cfg(test)]` for the same reason `FieldNames::all` is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub struct IdealNames {
    // Nine generic `AlgS.CommRing` lemmas.
    pub zero_add: NameId,
    pub neg_add_l: NameId,
    pub neg_zero: NameId,
    pub zero_mul: NameId,
    pub mul_neg_r: NameId,
    pub mul_neg_l: NameId,
    pub neg_add_dist: NameId,
    pub add_swap_mid: NameId,
    pub add_regroup: NameId,
    // The predicate and its five accessors.
    pub is_ideal: NameId,
    pub respects: NameId,
    pub mem_zero: NameId,
    pub closed_add: NameId,
    pub closed_neg: NameId,
    pub absorb: NameId,
    // Three instances, each with its `IsIdeal` proof.
    pub bot: NameId,
    pub top: NameId,
    pub principal: NameId,
    pub bot_is_ideal: NameId,
    pub top_is_ideal: NameId,
    pub principal_is_ideal: NameId,
    // The quotient.
    pub quot_equiv: NameId,
    pub of_equiv: NameId,
    pub quot_refl: NameId,
    pub quot_symm: NameId,
    pub quot_trans: NameId,
    pub quot_add_congr: NameId,
    pub quot_neg_congr: NameId,
    pub quot_mul_congr: NameId,
    pub quotient: NameId,
    pub quotient_equiv: NameId,
}

#[cfg(test)]
impl IdealNames {
    /// Every declaration this module introduces, derived from the struct's
    /// own fields — the population the sweeps in `ideal_setoid_tests` run
    /// over. Deliberately NOT called `all`: the trusted-core guard resolves
    /// method names loosely and a generic one joins its closure.
    pub fn owned_names(&self) -> [NameId; 31] {
        [
            self.zero_add,
            self.neg_add_l,
            self.neg_zero,
            self.zero_mul,
            self.mul_neg_r,
            self.mul_neg_l,
            self.neg_add_dist,
            self.add_swap_mid,
            self.add_regroup,
            self.is_ideal,
            self.respects,
            self.mem_zero,
            self.closed_add,
            self.closed_neg,
            self.absorb,
            self.bot,
            self.top,
            self.principal,
            self.bot_is_ideal,
            self.top_is_ideal,
            self.principal_is_ideal,
            self.quot_equiv,
            self.of_equiv,
            self.quot_refl,
            self.quot_symm,
            self.quot_trans,
            self.quot_add_congr,
            self.quot_neg_congr,
            self.quot_mul_congr,
            self.quotient,
            self.quotient_equiv,
        ]
    }

    /// The ones that are `Definition`s; the rest are checked `Theorem`s.
    pub fn definition_names(&self) -> [NameId; 6] {
        [
            self.is_ideal,
            self.bot,
            self.top,
            self.principal,
            self.quot_equiv,
            self.quotient,
        ]
    }
}

/// Declare `AlgS.Ideal.*` — ADR-1676. Needs the `AlgS.CommRing` record and
/// four `AlgS.*` ring lemmas, so it lands beside the other `AlgS` subobject
/// layers in the nat prelude's build order.
pub(crate) fn declare_ideal_setoid(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    comm_ring: &RecordNames,
    deps: IdealDeps,
    algs_p: NameId,
) -> Result<IdealNames, KernelError> {
    let ns = k.name_str(algs_p, "Ideal");

    // -- the nine generic ring lemmas --------------------------------------
    let zero_add = declare_zero_add(k, comm_ring, ns)?;
    let neg_add_l = declare_neg_add_l(k, comm_ring, ns)?;
    let neg_zero = declare_neg_zero(k, comm_ring, zero_add, ns)?;
    let zero_mul = declare_zero_mul(k, comm_ring, &deps, ns)?;
    let mul_neg_r = declare_mul_neg_r(k, comm_ring, &deps, ns)?;
    let mul_neg_l = declare_mul_neg_l(k, comm_ring, mul_neg_r, ns)?;
    let neg_add_dist = declare_neg_add_dist(k, comm_ring, &deps, ns)?;
    let add_swap_mid = declare_add_swap_mid(k, comm_ring, ns)?;
    let add_regroup = declare_add_regroup(k, comm_ring, ns)?;

    // -- the predicate and its accessors -----------------------------------
    let is_ideal = declare_is_ideal(k, lg, comm_ring, ns)?;
    let respects = declare_accessor(k, lg, comm_ring, is_ideal, 0, "respects", ns)?;
    let mem_zero = declare_accessor(k, lg, comm_ring, is_ideal, 1, "mem_zero", ns)?;
    let closed_add = declare_accessor(k, lg, comm_ring, is_ideal, 2, "closedAdd", ns)?;
    let closed_neg = declare_accessor(k, lg, comm_ring, is_ideal, 3, "closedNeg", ns)?;
    let absorb = declare_accessor(k, lg, comm_ring, is_ideal, 4, "absorb", ns)?;
    let acc = AccNames {
        respects,
        mem_zero,
        closed_add,
        closed_neg,
        absorb,
    };

    // -- three instances ---------------------------------------------------
    let bot = declare_bot(k, comm_ring, ns)?;
    let top = declare_top(k, lg, comm_ring, ns)?;
    let principal = declare_principal(k, lg, l1, comm_ring, ns)?;
    let bot_is_ideal = declare_bot_is_ideal(
        k, lg, comm_ring, &deps, is_ideal, bot, zero_add, neg_zero, ns,
    )?;
    let top_is_ideal = declare_top_is_ideal(k, lg, comm_ring, is_ideal, top, ns)?;
    let principal_is_ideal = declare_principal_is_ideal(
        k, lg, l1, comm_ring, is_ideal, principal, zero_mul, mul_neg_l, ns,
    )?;

    // -- the quotient ------------------------------------------------------
    let quot_equiv = declare_quot_equiv(k, comm_ring, ns)?;
    let of_equiv = declare_of_equiv(k, comm_ring, is_ideal, acc, ns)?;
    let quot_refl = declare_quot_refl(k, comm_ring, is_ideal, of_equiv, ns)?;
    let quot_symm = declare_quot_symm(k, comm_ring, &deps, is_ideal, acc, neg_add_dist, ns)?;
    let quot_trans = declare_quot_trans(
        k,
        comm_ring,
        is_ideal,
        acc,
        add_regroup,
        neg_add_l,
        zero_add,
        ns,
    )?;
    let quot_add_congr =
        declare_quot_add_congr(k, comm_ring, is_ideal, acc, add_swap_mid, neg_add_dist, ns)?;
    let quot_neg_congr = declare_quot_neg_congr(k, comm_ring, is_ideal, acc, neg_add_dist, ns)?;
    let quot_mul_congr = declare_quot_mul_congr(
        k,
        comm_ring,
        is_ideal,
        acc,
        add_regroup,
        neg_add_l,
        zero_add,
        mul_neg_r,
        ns,
    )?;
    let quotient = declare_quotient(
        k,
        comm_ring,
        is_ideal,
        QuotNames {
            of_equiv,
            refl: quot_refl,
            symm: quot_symm,
            trans: quot_trans,
            add_congr: quot_add_congr,
            neg_congr: quot_neg_congr,
            mul_congr: quot_mul_congr,
        },
        ns,
    )?;
    let quotient_equiv =
        declare_quotient_equiv(k, lg, comm_ring, is_ideal, quotient, quot_equiv, ns)?;

    Ok(IdealNames {
        zero_add,
        neg_add_l,
        neg_zero,
        zero_mul,
        mul_neg_r,
        mul_neg_l,
        neg_add_dist,
        add_swap_mid,
        add_regroup,
        is_ideal,
        respects,
        mem_zero,
        closed_add,
        closed_neg,
        absorb,
        bot,
        top,
        principal,
        bot_is_ideal,
        top_is_ideal,
        principal_is_ideal,
        quot_equiv,
        of_equiv,
        quot_refl,
        quot_symm,
        quot_trans,
        quot_add_congr,
        quot_neg_congr,
        quot_mul_congr,
        quotient,
        quotient_equiv,
    })
}

// ---------------------------------------------------------------------------
// Tests. Every assertion reads the KERNEL, never the source text.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod ideal_setoid_tests {
    use super::*;
    use crate::build_logic_prelude;
    use crate::nat_prelude::structures as algeq;
    use crate::nat_prelude::structures_setoid::{
        StructuresSExtraNames, StructuresSRecordNames, declare_structures_s_all,
        declare_structures_s_extra, intern_structures_s_names,
    };

    struct Fixture {
        lg: LogicPrelude,
        st: StructuresSRecordNames,
        extra: StructuresSExtraNames,
        deps: IdealDeps,
        id: IdealNames,
    }

    /// Build only what `AlgS.Ideal.*` needs: the logic prelude, the `Alg.*`
    /// spine (the `AlgS` extras project through it), the `AlgS.*` spine, its
    /// extras, and then the ideal layer. Much cheaper than the whole nat
    /// prelude, and it fails at the FIRST bad declaration.
    fn build(k: &mut Kernel) -> Fixture {
        let lg = build_logic_prelude(k).expect("logic prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let alg_p = algeq::intern_structures_names(k);
        let alg_st = algeq::declare_structures_all(k, &alg_p, &lg).expect("Alg spine builds");
        let p = intern_structures_s_names(k);
        let st = declare_structures_s_all(k, &p, &lg).expect("AlgS spine builds");
        let extra = declare_structures_s_extra(k, &lg, &p, &st, &alg_p, &alg_st)
            .expect("AlgS extras must admit");
        let deps = IdealDeps {
            comm_ring_to_ring_s: extra.comm_ring_to_ring_s,
            mul_zero: extra.mul_zero,
            mul_neg_one: extra.mul_neg_one,
            neg_neg: extra.neg_neg,
        };
        let id = declare_ideal_setoid(k, &lg, l1, &st.comm_ring, deps, p.algs)
            .expect("the ideal layer and the quotient ring must admit");
        Fixture {
            lg,
            st,
            extra,
            deps,
            id,
        }
    }

    #[test]
    fn the_ideal_layer_admits_by_the_setoid_route() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let names = f.id.owned_names();
        assert_eq!(names.len(), 31, "the owned population must be the real one");
        for name in names {
            assert!(
                k.environment().get(name).is_some(),
                "declaration missing from the environment"
            );
        }
    }

    /// **The headline claim**, read from `Kernel::axiom_footprint` — never
    /// from source text or a doc.
    #[test]
    fn the_ideal_layer_is_axiom_free() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.id.owned_names() {
            let footprint = k.axiom_footprint(name);
            assert!(
                footprint.is_empty(),
                "{} must have an empty axiom footprint, found {:?}",
                k.display_name(name),
                footprint
                    .iter()
                    .map(|n| k.display_name(*n).to_string())
                    .collect::<Vec<_>>()
            );
        }
    }

    /// The declaration KINDS, derived from the struct rather than a literal
    /// list: exactly the five names `definition_names` calls out are
    /// `Definition`s, and every other owned name is a checked `Theorem`.
    #[test]
    fn exactly_the_six_definitions_are_definitions_and_the_rest_are_checked_theorems() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let defs: std::collections::BTreeSet<NameId> =
            f.id.definition_names().into_iter().collect();
        let mut def_seen = 0usize;
        let mut thm_seen = 0usize;
        for name in f.id.owned_names() {
            let d = k
                .environment()
                .get(name)
                .expect("declaration must exist")
                .clone();
            if defs.contains(&name) {
                assert!(
                    matches!(d, Declaration::Definition { .. }),
                    "{} must be a Definition",
                    k.display_name(name)
                );
                def_seen += 1;
            } else {
                assert!(
                    matches!(d, Declaration::Theorem { .. }),
                    "{} must be a checked Theorem",
                    k.display_name(name)
                );
                thm_seen += 1;
            }
        }
        assert_eq!(def_seen, 6, "six definitions");
        assert_eq!(thm_seen, 25, "twenty-five checked theorems");
    }

    /// Every declaration's type renders, and every one is stated over an
    /// ABSTRACT `AlgS.CommRing`. Printed so a referee can read the
    /// statements out of the suite.
    #[test]
    fn the_ideal_types_render_over_an_abstract_comm_ring() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let mut mentions = 0usize;
        for name in f.id.owned_names() {
            let decl = k
                .environment()
                .get(name)
                .expect("declaration must exist")
                .clone();
            let rendered = k.render_lean(decl.ty());
            println!("{} : {rendered}", k.display_name(name));
            if rendered.contains("AlgS.CommRing") {
                mentions += 1;
            }
        }
        assert_eq!(
            mentions, 31,
            "every declaration must be stated over an abstract AlgS.CommRing"
        );
    }

    /// `AlgS.Ideal.quotient` really is an `AlgS.CommRing`-valued
    /// `Definition`, and its `carrier` field reduces to `R`'s own — the
    /// point of the setoid route.
    #[test]
    fn the_quotient_is_a_comm_ring_on_the_same_carrier() {
        use idx::comm_ring::CARRIER;
        let mut k = Kernel::new();
        let f = build(&mut k);
        let decl = k
            .environment()
            .get(f.id.quotient)
            .expect("quotient must exist")
            .clone();
        assert!(
            matches!(decl, Declaration::Definition { .. }),
            "the quotient must be a Definition producing an AlgS.CommRing"
        );
        let rendered = k.render_lean(decl.ty());
        assert!(
            rendered.trim_end_matches(')').ends_with("AlgS.CommRing"),
            "quotient's result type must be AlgS.CommRing, got {rendered}"
        );

        // `(quotient R I hI).carrier` is `def_eq` to `R.carrier`.
        let c = rctx(&mut k, &f.st.comm_ring);
        let i = k.fvar(I_FV);
        let hi = k.fvar(HI_FV);
        let quot = {
            let t = k.const_(f.id.quotient, vec![]);
            t_app(&mut k, t, &[c.r, i, hi])
        };
        let q_carrier = sel(&mut k, &f.st.comm_ring, CARRIER, quot);
        assert!(
            k.def_eq(q_carrier, c.carrier),
            "the quotient must live on the SAME carrier"
        );
    }

    // -- the mutation table -------------------------------------------------

    /// Rebuild `IsIdeal` with a chosen conjunct DROPPED, under a fresh name,
    /// and report whether the kernel still accepts `quotMulCongr`'s and
    /// `quotSymm`'s proof terms against the weakened accessors.
    ///
    /// Returns `(mul_congr_admits, symm_admits)`.
    fn mutant_without(k: &mut Kernel, f: &Fixture, drop_idx: usize, tag: &str) -> (bool, bool) {
        let c = rctx(k, &f.st.comm_ring);
        let i = k.fvar(I_FV);
        let props = five_stmts(k, &c, i);
        // The four surviving conjuncts, in order.
        let kept: Vec<ExprId> = props
            .iter()
            .enumerate()
            .filter(|(n, _)| *n != drop_idx)
            .map(|(_, p)| *p)
            .collect();
        let and_c = k.const_(f.lg.and, vec![]);
        let mut body = kept[3];
        for p in kept[..3].iter().rev() {
            body = app2(k, and_c, *p, body);
        }
        let value = close_ri(k, &c, body, true);
        let l0 = k.level_zero();
        let prop = k.sort(l0);
        let ty = arrow(k, c.pred_ty, prop);
        let ty = close_r(k, &c, ty, false);
        let anon = k.anon();
        let ns = k.name_str(anon, tag);
        let weak = definition(k, ns, "IsIdealMutant", ty, value)
            .expect("the weakened predicate itself must admit -- it is a smaller conjunction");

        // Accessors off the WEAKENED predicate. Only the four kept conjuncts
        // are reachable; asking for the dropped one is the whole point.
        let mut acc_names = [None; N_CONJ];
        let mut slot = 0usize;
        for (n, name) in [
            (0usize, "respects"),
            (1, "mem_zero"),
            (2, "closedAdd"),
            (3, "closedNeg"),
            (4, "absorb"),
        ] {
            if n == drop_idx {
                continue;
            }
            let a = mutant_accessor(k, f, weak, &kept, slot, name, ns);
            acc_names[n] = a;
            slot += 1;
        }

        // If the dropped conjunct has no accessor, the proofs that need it
        // cannot even be assembled -- which is the finding. Substitute the
        // `respects` accessor's name so the call still type-checks in Rust
        // and the KERNEL is the thing that refuses.
        let sub = acc_names[0].expect("respects always survives here");
        let acc = AccNames {
            respects: acc_names[0].unwrap_or(sub),
            mem_zero: acc_names[1].unwrap_or(sub),
            closed_add: acc_names[2].unwrap_or(sub),
            closed_neg: acc_names[3].unwrap_or(sub),
            absorb: acc_names[4].unwrap_or(sub),
        };

        let mul = declare_quot_mul_congr(
            k,
            &f.st.comm_ring,
            weak,
            acc,
            f.id.add_regroup,
            f.id.neg_add_l,
            f.id.zero_add,
            f.id.mul_neg_r,
            ns,
        );
        let symm = declare_quot_symm(
            k,
            &f.st.comm_ring,
            &f.deps,
            weak,
            acc,
            f.id.neg_add_dist,
            ns,
        );
        (mul.is_ok(), symm.is_ok())
    }

    fn mutant_accessor(
        k: &mut Kernel,
        f: &Fixture,
        weak: NameId,
        kept: &[ExprId],
        which: usize,
        suffix: &str,
        ns: NameId,
    ) -> Option<NameId> {
        let c = rctx(k, &f.st.comm_ring);
        let i = k.fvar(I_FV);
        let hyp_ty = {
            let t = k.const_(weak, vec![]);
            app2(k, t, c.r, i)
        };
        let h = k.fvar(HI_FV);
        // `And.left`/`And.right` chain over the FOUR kept conjuncts.
        let and_c = k.const_(f.lg.and, vec![]);
        let mut tails = vec![kept[3]];
        for p in kept[..3].iter().rev() {
            let last = *tails.last().expect("non-empty");
            tails.push(app2(k, and_c, *p, last));
        }
        tails.reverse();
        let mut cur = h;
        for (n, prop) in kept.iter().enumerate().take(which) {
            let and_right = k.const_(f.lg.and_right, vec![]);
            cur = t_app(k, and_right, &[*prop, tails[n + 1], cur]);
        }
        let proof = if which == 3 {
            cur
        } else {
            let and_left = k.const_(f.lg.and_left, vec![]);
            t_app(k, and_left, &[kept[which], tails[which + 1], cur])
        };
        let value = close_rih(k, &c, hyp_ty, proof, true);
        let ty = close_rih(k, &c, hyp_ty, kept[which], false);
        theorem(k, ns, suffix, ty, value).ok()
    }

    /// **Mutant 1 (the absorbing law).** Drop `absorb` from `IsIdeal` and
    /// the quotient's MULTIPLICATIVE congruence must become unprovable —
    /// while `equivSymm`, which does not use it, must still go through. The
    /// second half is the positive control: without it a mutant that broke
    /// everything (including the harness) would look like a pass.
    #[test]
    fn dropping_the_absorbing_law_kills_the_quotients_multiplicative_congruence() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let (mul_ok, symm_ok) = mutant_without(&mut k, &f, 4, "AbsorbDropped");
        assert!(
            !mul_ok,
            "with `absorb` dropped the kernel still admitted quotMulCongr -- \
             the absorbing law is then not load-bearing and `IsIdeal` is \
             carrying a field nothing needs"
        );
        assert!(
            symm_ok,
            "positive control: `equivSymm` does not use `absorb` and must \
             still admit; if it fails the mutant broke the harness, not the \
             mathematics"
        );
    }

    /// **Mutant 1's mirror.** Drop `closedNeg` instead: now `equivSymm` must
    /// fail and `mulCongr` must still succeed. The two mutants together show
    /// the two conjuncts are load-bearing in DISJOINT places, which is the
    /// reason `closedNeg` is an explicit conjunct rather than derived from
    /// `absorb`.
    #[test]
    fn dropping_closed_neg_kills_symmetry_and_leaves_multiplicative_congruence() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let (mul_ok, symm_ok) = mutant_without(&mut k, &f, 3, "ClosedNegDropped");
        assert!(
            !symm_ok,
            "with `closedNeg` dropped the kernel still admitted quotSymm"
        );
        assert!(
            mul_ok,
            "positive control: `mulCongr` does not use `closedNeg` and must \
             still admit"
        );
    }

    /// **Mutant 2 (the symmetry step reversed).** `quotSymm`'s chain ends
    /// with `R.addComm (-x) y : (-x) + y ~ y + (-x)`. Reverse that step —
    /// use `R.addComm y (-x)`, which proves the equivalence the OTHER way
    /// round — and the kernel must refuse the assembled proof. Paired in the
    /// same invocation with the unreversed build, which must succeed.
    #[test]
    fn reversing_the_symmetry_steps_last_leg_is_refused() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let c = rctx(&mut k, &f.st.comm_ring);
        let i = k.fvar(I_FV);
        let hi_ty = is_ideal_at(&mut k, &c, f.id.is_ideal, i);
        let hi = k.fvar(HI_FV);
        let x = k.fvar(X_FV);
        let y = k.fvar(Y_FV);
        let h = k.fvar(H1_FV);

        let ny = c.ng(&mut k, y);
        let nx = c.ng(&mut k, x);
        let diff = c.pl(&mut k, x, ny);
        let ndiff = c.ng(&mut k, diff);
        let nny = c.ng(&mut k, ny);
        let mid = c.pl(&mut k, nx, nny);
        let mid2 = c.pl(&mut k, nx, y);
        let goal = c.pl(&mut k, y, nx);

        // Both variants share everything up to the last leg.
        let build_variant = |k: &mut Kernel, reversed: bool| -> ExprId {
            let mut ch = Chain::start(k, &c, ndiff);
            let nad = {
                let t = k.const_(f.id.neg_add_dist, vec![]);
                t_app(k, t, &[c.r, x, ny])
            };
            ch.step(k, &c, mid, nad);
            let nn = at_ring(k, &c, &f.deps, f.deps.neg_neg);
            let nn_y = k.app(nn, y);
            let rnx = c.rf(k, nx);
            let s2 = c.addc(k, nx, nx, nny, y, rnx, nn_y);
            ch.step(k, &c, mid2, s2);
            let s3 = if reversed {
                t_app(k, c.add_comm, &[y, nx])
            } else {
                t_app(k, c.add_comm, &[nx, y])
            };
            ch.step(k, &c, goal, s3);

            let closed_neg = acc_at(k, &c, f.id.closed_neg, i, hi);
            let neg_h = t_app(k, closed_neg, &[diff, h]);
            let respects = acc_at(k, &c, f.id.respects, i, hi);
            let body = t_app(k, respects, &[ndiff, goal, ch.p, neg_h]);
            let hyp = k.app(i, diff);
            let v = lam_over(k, H1_FV, hyp, body);
            let v = lam_over(k, Y_FV, c.carrier, v);
            let v = lam_over(k, X_FV, c.carrier, v);
            close_rih(k, &c, hi_ty, v, true)
        };

        let hyp = k.app(i, diff);
        let concl = k.app(i, goal);
        let ty = pi_over(&mut k, H1_FV, hyp, concl);
        let ty = pi_over(&mut k, Y_FV, c.carrier, ty);
        let ty = pi_over(&mut k, X_FV, c.carrier, ty);
        let ty = close_rih(&mut k, &c, hi_ty, ty, false);

        let good = build_variant(&mut k, false);
        let anon = k.anon();
        let ns = k.name_str(anon, "SymmMutant");
        let ok = theorem(&mut k, ns, "unreversed", ty, good);
        assert!(
            ok.is_ok(),
            "positive control in the SAME invocation: the unreversed chain \
             must admit, got {ok:?}"
        );

        let bad = build_variant(&mut k, true);
        let bad_res = theorem(&mut k, ns, "reversed", ty, bad);
        assert!(
            bad_res.is_err(),
            "the kernel admitted a symmetry chain whose last leg proves the \
             equivalence the wrong way round"
        );
    }

    /// A kernel REJECTION control that is not about a mutant of our own
    /// making: `principal_isIdeal`'s proof term is not a proof that the ZERO
    /// ideal is an ideal, and the kernel says so. Paired with the positive:
    /// `bot_isIdeal`'s own term IS accepted at the same statement.
    #[test]
    fn the_principal_ideals_proof_is_not_a_proof_about_the_zero_ideal() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let c = rctx(&mut k, &f.st.comm_ring);
        let bot_r = {
            let t = k.const_(f.id.bot, vec![]);
            k.app(t, c.r)
        };
        let ty = is_ideal_at(&mut k, &c, f.id.is_ideal, bot_r);
        let ty = close_r(&mut k, &c, ty, false);

        let anon = k.anon();
        let ns = k.name_str(anon, "BotControl");

        // Positive: `bot_isIdeal`'s own value at that statement.
        let good = {
            let d = k
                .environment()
                .get(f.id.bot_is_ideal)
                .expect("bot_isIdeal must exist")
                .clone();
            match d {
                Declaration::Theorem { value, .. } => value,
                _ => panic!("bot_isIdeal must be a Theorem"),
            }
        };
        assert!(
            theorem(&mut k, ns, "positive", ty, good).is_ok(),
            "positive control: bot_isIdeal's own proof term must be accepted \
             at its own statement"
        );

        // Negative: `principal_isIdeal`'s value at the same statement.
        let bad = {
            let d = k
                .environment()
                .get(f.id.principal_is_ideal)
                .expect("principal_isIdeal must exist")
                .clone();
            match d {
                Declaration::Theorem { value, .. } => value,
                _ => panic!("principal_isIdeal must be a Theorem"),
            }
        };
        assert!(
            theorem(&mut k, ns, "negative", ty, bad).is_err(),
            "the kernel accepted the principal ideal's proof as a proof about \
             the ZERO ideal"
        );
    }

    /// **Deliverable 3's obstruction, measured rather than asserted.** The
    /// brief asked whether the first isomorphism theorem in RING form
    /// (`R/ker f ≅ im f`) is within reach from `AlgS.Hom.firstIso`'s shape by
    /// transport. It is not, and the reason is readable off the two types:
    /// `firstIso` (and `firstIsoClassical`) quantify over `AlgS.Group`
    /// ONLY -- one operation, one `fMul` -- while a ring quotient is an
    /// `AlgS.CommRing`. There is no coercion between the two records in this
    /// kernel, so the ring form is a new binder stack, not a transport.
    ///
    /// The positive control is in the same invocation: `AlgS.Ideal.quotient`
    /// DOES mention `AlgS.CommRing`, so a rendering that had simply stopped
    /// working could not make this test pass.
    #[test]
    fn the_group_first_isomorphism_theorem_says_nothing_about_rings() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for (name, label) in [
            (f.extra.hom_first_iso, "AlgS.Hom.firstIso"),
            (f.extra.hom_quotient, "AlgS.Hom.quotient"),
        ] {
            let decl = k
                .environment()
                .get(name)
                .expect("the group-level first isomorphism layer must exist")
                .clone();
            let rendered = k.render_lean(decl.ty());
            assert!(
                rendered.contains("AlgS.Group"),
                "{label} must be stated over AlgS.Group"
            );
            assert!(
                !rendered.contains("AlgS.CommRing"),
                "{label} mentions AlgS.CommRing -- the ring form may now be a \
                 transport after all, and this lane's recorded obstruction is \
                 stale: {rendered}"
            );
        }
        // Positive control, same invocation.
        let q = k
            .environment()
            .get(f.id.quotient)
            .expect("the ideal quotient must exist")
            .clone();
        assert!(
            k.render_lean(q.ty()).contains("AlgS.CommRing"),
            "positive control: AlgS.Ideal.quotient must mention AlgS.CommRing"
        );
    }

    // -- the evaluation test ------------------------------------------------

    /// **Evaluation test at concrete, small, discriminating arguments.** The
    /// type-checker cannot tell a `Definition` computes the wrong value, so
    /// `AlgS.Ideal.principal` is instantiated at the integers through
    /// `AlgS.CommRing.ofAlg(Int.commRing)` and its value is READ BACK by
    /// reduction:
    ///
    /// - `AlgS.Ideal.principal R 2 4` unfolds to exactly
    ///   `Exists Int (fun r => R.equiv 4 (R.mul r 2))`;
    /// - the membership `4 ∈ (2)` is PROVED by supplying the witness `2` and
    ///   `Eq.refl 4`, which type-checks only because `Int.mul 2 2` reduces to
    ///   `4`;
    /// - the discriminating half, in the SAME invocation: the same term with
    ///   witness `1` is NOT a proof, because `1 * 2` is `2`. A `principal`
    ///   that ignored either argument would accept it.
    ///
    /// Magnitudes are 1, 2 and 4 deliberately: every `Nat` numeral
    /// underneath is unary.
    #[test]
    fn the_principal_ideal_of_two_contains_four_at_the_integers() {
        use crate::rat_prelude::build_rat_prelude;
        use idx::comm_ring::{CARRIER, EQUIV, MUL};
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let extra = np.structures_s_extra;
        let cr = np.structures_s.comm_ring;

        let int_comm_ring = k.const_(rp.algebra.int_comm_ring, vec![]);
        let ofalg = k.const_(extra.comm_ring_ofalg, vec![]);
        let r = k.app(ofalg, int_comm_ring);

        let one = int_lit(&mut k, &rp, 1);
        let two = int_lit(&mut k, &rp, 2);
        let four = int_lit(&mut k, &rp, 4);

        // `AlgS.Ideal.principal` resolved by NAME off the `AlgS` root -- the
        // ideal layer is built by `build_nat_prelude`, so it is already in
        // this environment; nothing is threaded through `NatPrelude`.
        let algs = np.structures_s_names.algs;
        let ideal_ns = k.name_str(algs, "Ideal");
        let principal = k.name_str(ideal_ns, "principal");
        assert!(
            k.environment().get(principal).is_some(),
            "AlgS.Ideal.principal must be live in the rat prelude's environment"
        );
        let prin_c = k.const_(principal, vec![]);
        let member = t_app(&mut k, prin_c, &[r, two, four]);

        // The shape `principal` MUST unfold to, rebuilt from `R`'s own
        // selectors rather than assumed.
        let carrier = sel(&mut k, &cr, CARRIER, r);
        let equiv_sel = sel(&mut k, &cr, EQUIV, r);
        let mul_sel = sel(&mut k, &cr, MUL, r);
        let pred = {
            let w = k.fvar(W_FV);
            let w2 = app2(&mut k, mul_sel, w, two);
            let body = app2(&mut k, equiv_sel, four, w2);
            lam_over(&mut k, W_FV, carrier, body)
        };
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let expected = {
            let ex = k.const_(rp.int.logic.exists_, vec![l1]);
            t_app(&mut k, ex, &[carrier, pred])
        };
        assert!(
            k.def_eq(member, expected),
            "`AlgS.Ideal.principal R 2 4` must unfold to \
             `Exists R.carrier (fun r => R.equiv 4 (R.mul r 2))`"
        );

        // The membership proof: witness 2, and `Eq.refl 4` -- which only
        // type-checks because `Int.mul 2 2` REDUCES to `4`.
        let int_ty = k.const_(rp.int.z, vec![]);
        let refl = k.const_(rp.int.logic.eq_refl, vec![l1]);
        let proof = t_app(&mut k, refl, &[int_ty, four]);
        let ex_intro_c = k.const_(rp.int.logic.exists_intro, vec![l1]);
        let good = t_app(&mut k, ex_intro_c, &[carrier, pred, two, proof]);
        let inferred = k
            .infer(good)
            .expect("`Exists.intro 2 (Eq.refl 4)` must infer a type");
        assert!(
            k.def_eq(inferred, member),
            "witness 2 must prove that 4 lies in the ideal generated by 2"
        );

        // Discriminating negative, same invocation: witness 1 does not work,
        // because `1 * 2` is `2` and not `4`.
        let bad = t_app(&mut k, ex_intro_c, &[carrier, pred, one, proof]);
        let bad_ok = match k.infer(bad) {
            Err(_) => false,
            Ok(t) => k.def_eq(t, member),
        };
        assert!(
            !bad_ok,
            "witness 1 must NOT prove 4 is in the ideal generated by 2 -- a \
             `principal` that ignored its generator would accept it"
        );
    }

    /// Small non-negative integer literal: `Int.ofNat (Nat.succ^n Nat.zero)`.
    fn int_lit(k: &mut Kernel, rp: &crate::rat_prelude::RatPrelude, n: u32) -> ExprId {
        let mut nat = k.const_(rp.int.nat.zero, vec![]);
        let succ = k.const_(rp.int.nat.succ, vec![]);
        for _ in 0..n {
            nat = k.app(succ, nat);
        }
        let of_nat = k.const_(rp.int.of_nat, vec![]);
        k.app(of_nat, nat)
    }
}
