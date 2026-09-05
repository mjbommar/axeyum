//! ADR-1616 (roadmap W1-10): the finite probability layer, stated **once**
//! over `(R : AlgS.OrderedRing)`.
//!
//! `rat_prelude/probability.rs` proves roughly thirty finite-probability
//! theorems over `ℚ`. Every one of them is stated in `add`/`mul`/`neg`/
//! `zero`/`one`/`le` and an equality — and `AlgS.OrderedRing` (ADR-1592)
//! carries exactly that vocabulary for **both** carriers whose equality
//! regimes differ (`ℚ`, where `equiv` is `Eq`, and `CReal`, where it is
//! `CReal.Equiv`). So the layer generalizes without a bridge, and this file
//! is where it is stated.
//!
//! **What the record does not carry, and what that costs.** ADR-1592 chose
//! `AlgS.OrderedRing`'s seven order fields from `Alg.OrderedRing`, whose own
//! seven came from what `linarith` needed. The multiplicative order law in
//! that set is `mul_nonneg` alone. Every expectation bound in the `ℚ`
//! development is instead built on `Rat.mul_le_mul_of_nonneg_right`, a
//! *primitive* there. Recovering it here costs three auxiliary generic ring
//! lemmas — [`declare_zero_mul`], [`declare_neg_mul`] and
//! [`declare_sub_nonneg_of_le`] — none of which the `Eq`-flavored spine had
//! either. This is ADR-1612's lesson in a second setting: a record whose
//! fields were drawn from one development's needs does not re-derive another
//! development's primitives for free; it re-derives them at a price, and the
//! price is the interesting number.
//!
//! **`AlgS.OrderedRing.toRingS`.** `AlgS.mul_zero`, `AlgS.add_left_cancel`
//! and `AlgS.sub` are all stated over `AlgS.Ring`, and ADR-1592 declared no
//! forgetful projection from `AlgS.OrderedRing` down to it — `AlgS.CommRing.
//! toRingS` was the only one the spine had. Since `AlgS.OrderedRing`'s first
//! 22 fields ARE `AlgS.Ring`'s, in order, the projection is the same prefix
//! `mk_instance` `CommRing.toRingS` already is, and declaring it here makes
//! every existing `AlgS.Ring`-level theorem reachable from an ordered ring.
//!
//! Every theorem in this file is proved from the record's fields alone: no
//! axiom, no classical principle, no carrier-specific step.

use super::RatPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::{RecordNames, mk_instance, sel};
use crate::nat_prelude::structures_setoid::idx::ordered_ring as oidx;

/// The names this module declares, all under the `AlgS.OrderedRing` root
/// (matching ADR-1592's own derived lemmas `AlgS.OrderedRing.ofNat` and
/// `AlgS.OrderedRing.add_le_add`, which take the same leading record
/// argument).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProbSNames {
    pub to_ring_s: NameId,
    pub to_group_s: NameId,
    pub zero_mul: NameId,
    pub neg_mul: NameId,
    pub sub_nonneg_of_le: NameId,
    pub mul_le_mul_of_nonneg_right: NameId,
    pub sum_range: NameId,
    pub sum_range_zero: NameId,
    pub sum_range_succ: NameId,
    pub sum_range_congr: NameId,
    pub sum_range_add: NameId,
    pub mul_sum_range: NameId,
    pub sum_range_le: NameId,
    pub sum_range_nonneg: NameId,
    pub is_distribution: NameId,
    pub expectation: NameId,
    pub expectation_add: NameId,
    pub expectation_smul: NameId,
    pub expectation_const: NameId,
    pub expectation_nonneg: NameId,
    pub expectation_le: NameId,
    pub markov_inequality: NameId,
    pub variance: NameId,
    pub variance_nonneg: NameId,
    pub covariance: NameId,
    pub covariance_comm: NameId,
    pub covariance_eq: NameId,
    pub independent: NameId,
    pub uncorrelated_of_independent: NameId,
}

/// Intern every name this module declares.
pub(crate) fn intern_probability_s(k: &mut Kernel) -> ProbSNames {
    let anon = k.anon();
    let algs = k.name_str(anon, "AlgS");
    let root = k.name_str(algs, "OrderedRing");
    ProbSNames {
        to_ring_s: k.name_str(root, "toRingS"),
        to_group_s: k.name_str(root, "toGroupS"),
        zero_mul: k.name_str(root, "zero_mul"),
        neg_mul: k.name_str(root, "neg_mul"),
        sub_nonneg_of_le: k.name_str(root, "sub_nonneg_of_le"),
        mul_le_mul_of_nonneg_right: k.name_str(root, "mul_le_mul_of_nonneg_right"),
        sum_range: k.name_str(root, "sumRange"),
        sum_range_zero: k.name_str(root, "sumRange_zero"),
        sum_range_succ: k.name_str(root, "sumRange_succ"),
        sum_range_congr: k.name_str(root, "sumRange_congr"),
        sum_range_add: k.name_str(root, "sumRange_add"),
        mul_sum_range: k.name_str(root, "mul_sumRange"),
        sum_range_le: k.name_str(root, "sumRange_le"),
        sum_range_nonneg: k.name_str(root, "sumRange_nonneg"),
        is_distribution: k.name_str(root, "IsDistribution"),
        expectation: k.name_str(root, "expectation"),
        expectation_add: k.name_str(root, "expectation_add"),
        expectation_smul: k.name_str(root, "expectation_smul"),
        expectation_const: k.name_str(root, "expectation_const"),
        expectation_nonneg: k.name_str(root, "expectation_nonneg"),
        expectation_le: k.name_str(root, "expectation_le"),
        markov_inequality: k.name_str(root, "markov_inequality"),
        variance: k.name_str(root, "variance"),
        variance_nonneg: k.name_str(root, "variance_nonneg"),
        covariance: k.name_str(root, "covariance"),
        covariance_comm: k.name_str(root, "covariance_comm"),
        covariance_eq: k.name_str(root, "covariance_eq"),
        independent: k.name_str(root, "Independent"),
        uncorrelated_of_independent: k.name_str(root, "uncorrelated_of_independent"),
    }
}

// ---------------------------------------------------------------------------
// Projections: the record's fields, read once per builder.
// ---------------------------------------------------------------------------

/// Every `AlgS.OrderedRing` field this file uses, projected at one record
/// value `r`.
///
/// A plain struct of `ExprId`s rather than repeated `sel` calls: each proof
/// below uses ten to twenty of them, and reading them once keeps the proof
/// terms readable and the `sel` spelling in exactly one place.
#[derive(Clone, Copy)]
struct Rec {
    carrier: ExprId,
    equiv: ExprId,
    erefl: ExprId,
    esymm: ExprId,
    etrans: ExprId,
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
    mul_one_r: ExprId,
    distrib_l: ExprId,
    distrib_r: ExprId,
    neg: ExprId,
    neg_add: ExprId,
    le: ExprId,
    le_congr: ExprId,
    le_refl: ExprId,
    le_trans: ExprId,
    add_le_add_left: ExprId,
    mul_nonneg: ExprId,
}

fn proj_one(d: &mut IntDev<'_>, rn: &RecordNames, i: usize, r: ExprId) -> ExprId {
    let k = d.kernel();
    sel(k, rn, i, r)
}

fn proj(d: &mut IntDev<'_>, rn: &RecordNames, r: ExprId) -> Rec {
    Rec {
        carrier: proj_one(d, rn, oidx::CARRIER, r),
        equiv: proj_one(d, rn, oidx::EQUIV, r),
        erefl: proj_one(d, rn, oidx::EQUIV_REFL, r),
        esymm: proj_one(d, rn, oidx::EQUIV_SYMM, r),
        etrans: proj_one(d, rn, oidx::EQUIV_TRANS, r),
        zero: proj_one(d, rn, oidx::ZERO, r),
        one: proj_one(d, rn, oidx::ONE, r),
        add: proj_one(d, rn, oidx::ADD, r),
        mul: proj_one(d, rn, oidx::MUL, r),
        add_congr: proj_one(d, rn, oidx::ADD_CONGR, r),
        mul_congr: proj_one(d, rn, oidx::MUL_CONGR, r),
        add_assoc: proj_one(d, rn, oidx::ADD_ASSOC, r),
        add_comm: proj_one(d, rn, oidx::ADD_COMM, r),
        add_zero: proj_one(d, rn, oidx::ADD_ZERO, r),
        mul_assoc: proj_one(d, rn, oidx::MUL_ASSOC, r),
        mul_one_r: proj_one(d, rn, oidx::MUL_ONE_R, r),
        distrib_l: proj_one(d, rn, oidx::DISTRIB_L, r),
        distrib_r: proj_one(d, rn, oidx::DISTRIB_R, r),
        neg: proj_one(d, rn, oidx::NEG, r),
        neg_add: proj_one(d, rn, oidx::NEG_ADD, r),
        le: proj_one(d, rn, oidx::LE, r),
        le_congr: proj_one(d, rn, oidx::LE_CONGR, r),
        le_refl: proj_one(d, rn, oidx::LE_REFL, r),
        le_trans: proj_one(d, rn, oidx::LE_TRANS, r),
        add_le_add_left: proj_one(d, rn, oidx::ADD_LE_ADD_LEFT, r),
        mul_nonneg: proj_one(d, rn, oidx::MUL_NONNEG, r),
    }
}

// --- term shorthands -------------------------------------------------------

fn eqv(d: &mut IntDev<'_>, c: Rec, a: ExprId, b: ExprId) -> ExprId {
    d.apply(c.equiv, &[a, b])
}
fn radd(d: &mut IntDev<'_>, c: Rec, a: ExprId, b: ExprId) -> ExprId {
    d.apply(c.add, &[a, b])
}
fn rmul(d: &mut IntDev<'_>, c: Rec, a: ExprId, b: ExprId) -> ExprId {
    d.apply(c.mul, &[a, b])
}
fn rneg(d: &mut IntDev<'_>, c: Rec, a: ExprId) -> ExprId {
    d.apply(c.neg, &[a])
}
fn rsub(d: &mut IntDev<'_>, c: Rec, a: ExprId, b: ExprId) -> ExprId {
    let nb = rneg(d, c, b);
    radd(d, c, a, nb)
}
fn rle(d: &mut IntDev<'_>, c: Rec, a: ExprId, b: ExprId) -> ExprId {
    d.apply(c.le, &[a, b])
}
fn refl(d: &mut IntDev<'_>, c: Rec, a: ExprId) -> ExprId {
    d.apply(c.erefl, &[a])
}
fn symm(d: &mut IntDev<'_>, c: Rec, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.apply(c.esymm, &[a, b, h])
}
fn trans(
    d: &mut IntDev<'_>,
    c: Rec,
    a: ExprId,
    b: ExprId,
    e: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    d.apply(c.etrans, &[a, b, e, h1, h2])
}
#[allow(clippy::too_many_arguments)]
fn acongr(
    d: &mut IntDev<'_>,
    c: Rec,
    a: ExprId,
    a2: ExprId,
    b: ExprId,
    b2: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    d.apply(c.add_congr, &[a, a2, b, b2, h1, h2])
}
#[allow(clippy::too_many_arguments)]
fn mcongr(
    d: &mut IntDev<'_>,
    c: Rec,
    a: ExprId,
    a2: ExprId,
    b: ExprId,
    b2: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    d.apply(c.mul_congr, &[a, a2, b, b2, h1, h2])
}
#[allow(clippy::too_many_arguments)]
fn lecongr(
    d: &mut IntDev<'_>,
    c: Rec,
    a: ExprId,
    a2: ExprId,
    b: ExprId,
    b2: ExprId,
    h1: ExprId,
    h2: ExprId,
    h: ExprId,
) -> ExprId {
    d.apply(c.le_congr, &[a, a2, b, b2, h1, h2, h])
}

/// The record's own type, `AlgS.OrderedRing`.
fn rec_ty(d: &mut IntDev<'_>, rn: &RecordNames) -> ExprId {
    d.kernel().const_(rn.ind, vec![])
}

/// `AlgS.OrderedRing.sumRange R f n`.
fn sum_range_of(d: &mut IntDev<'_>, names: &ProbSNames, r: ExprId, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(names.sum_range, &[r, f, n])
}

/// `AlgS.OrderedRing.expectation R X p n`.
fn expectation_of(
    d: &mut IntDev<'_>,
    names: &ProbSNames,
    r: ExprId,
    x: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    d.const_app(names.expectation, &[r, x, pf, n])
}

/// `AlgS.OrderedRing.covariance R X Y p n`.
fn covariance_of(
    d: &mut IntDev<'_>,
    names: &ProbSNames,
    r: ExprId,
    x: ExprId,
    y: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    d.const_app(names.covariance, &[r, x, y, pf, n])
}

/// `fun k => R.mul (X k) (p k)` — the weighted summand `expectation` sums,
/// rebuilt where a proof needs its literal shape (the same reason
/// `probability::weighted` exists on the `ℚ` side).
fn weighted(d: &mut IntDev<'_>, c: Rec, x: ExprId, pf: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let kv = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[kv]);
    let pk = d.apply(pf, &[kv]);
    let body = rmul(d, c, xk, pk);
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => R.add (X k) (Y k)`.
fn combined(d: &mut IntDev<'_>, c: Rec, x: ExprId, y: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let kv = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[kv]);
    let yk = d.apply(y, &[kv]);
    let body = radd(d, c, xk, yk);
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => R.mul a (X k)`.
fn scaled(d: &mut IntDev<'_>, c: Rec, a: ExprId, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let kv = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[kv]);
    let body = rmul(d, c, a, xk);
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => R.mul (X k) (Y k)` — the pointwise product.
fn pointwise_mul(d: &mut IntDev<'_>, c: Rec, x: ExprId, y: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let kv = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[kv]);
    let yk = d.apply(y, &[kv]);
    let body = rmul(d, c, xk, yk);
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => R.mul (X k − a) (Y k − b)` — the centred product `covariance`
/// sums, and (at `X = Y`, `a = b`) the squared deviation `variance` sums.
fn centred_product(
    d: &mut IntDev<'_>,
    c: Rec,
    x: ExprId,
    y: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let kv = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[kv]);
    let yk = d.apply(y, &[kv]);
    let dx = rsub(d, c, xk, a);
    let dy = rsub(d, c, yk, b);
    let body = rmul(d, c, dx, dy);
    d.lam_fv(k_fv, nat, body)
}

/// `∀ i, Nat.lt i bound → R.le R.zero (f i)`.
fn bounded_nonneg(d: &mut IntDev<'_>, c: Rec, f: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let nonneg = rle(d, c, c.zero, fi);
    let body = d.arrow(hyp, nonneg);
    d.pi_fv(i_fv, nat, body)
}

/// `∀ i, Nat.lt i bound → R.le (f i) (g i)`.
fn bounded_le(d: &mut IntDev<'_>, c: Rec, f: ExprId, g: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let body_le = rle(d, c, fi, gi);
    let body = d.arrow(hyp, body_le);
    d.pi_fv(i_fv, nat, body)
}

/// Restrict a bounded hypothesis `h : ∀ i, i < succ j → P i` to `∀ i, i < j →
/// P i`, and read off `P j` — the two halves every bounded induction step
/// needs, spelled once (the `ℚ` file repeats this block per theorem).
fn restrict(d: &mut IntDev<'_>, h: ExprId, j: ExprId, sj: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let np = d.prelude();
    let below = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.lt(i, j);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let le_succ_j = d.lemma(np.le_succ, &[j]);
        let lifted = d.lemma(np.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
        let applied = d.apply(h, &[i, lifted]);
        let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
        d.lam_fv(i_fv, nat, with_hi)
    };
    let at_j = {
        let lt_j_sj = d.lemma(np.lt_succ_self, &[j]);
        d.apply(h, &[j, lt_j_sj])
    };
    (below, at_j)
}

// ---------------------------------------------------------------------------
// `AlgS.OrderedRing.toRingS` — the forgetful prefix projection.
// ---------------------------------------------------------------------------

/// `AlgS.OrderedRing.toRingS : AlgS.OrderedRing → AlgS.Ring`.
///
/// `AlgS.OrderedRing`'s fields `0..=21` ARE `AlgS.Ring`'s, in order
/// (ADR-1592 built the record that way so `ofAlg` would type-check), so this
/// is the same prefix `mk_instance` `AlgS.CommRing.toRingS` already is. It
/// is what makes `AlgS.mul_zero`, `AlgS.add_left_cancel` and `AlgS.sub`
/// reachable from an ordered ring at all.
fn declare_to_ring_s(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    ring: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let mut args = Vec::with_capacity(oidx::NEG_ADD + 1);
    for i in 0..=oidx::NEG_ADD {
        args.push(proj_one(d, rn, i, r));
    }
    let value = {
        let k = d.kernel();
        mk_instance(k, ring, &args)
    };
    let ord_ty = rec_ty(d, rn);
    let value = d.lam_fv(r_fv, ord_ty, value);
    let ty = {
        let dom = rec_ty(d, rn);
        let cod = rec_ty(d, ring);
        d.arrow(dom, cod)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: names.to_ring_s,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `AlgS.OrderedRing.toGroupS : AlgS.OrderedRing → AlgS.Group`, the
/// **additive** group.
///
/// Not a prefix projection — `AlgS.Group` orders its fields differently, and
/// two of them (`identL`, `invL`) are not `AlgS.OrderedRing` fields at all;
/// both are derived from `addComm` against `addZero`/`negAdd`, exactly as
/// ADR-1590's test-only `ring_s_additive_group_value` derives them for
/// `AlgS.Ring`. Declaring it is what makes `AlgS.add_left_cancel` (stated
/// over `AlgS.Group`) reachable from an ordered ring, which
/// [`declare_zero_mul`] and [`declare_neg_mul`] both need.
fn declare_to_group_s(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    group: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let neg_congr = proj_one(d, rn, oidx::NEG_CONGR, r);

    // identL(a) : equiv (add zero a) a, via addComm(zero,a); addZero(a).
    let ident_l = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let add_za = radd(d, c, c.zero, a);
        let add_az = radd(d, c, a, c.zero);
        let comm_za = d.apply(c.add_comm, &[c.zero, a]);
        let az_a = d.apply(c.add_zero, &[a]);
        let body = trans(d, c, add_za, add_az, a, comm_za, az_a);
        d.lam_fv(a_fv, c.carrier, body)
    };
    // invL(b) : equiv (add (neg b) b) zero, via addComm(neg b,b); negAdd(b).
    let inv_l = {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let nb = rneg(d, c, b);
        let add_nbb = radd(d, c, nb, b);
        let add_bnb = radd(d, c, b, nb);
        let comm_nb_b = d.apply(c.add_comm, &[nb, b]);
        let na_b = d.apply(c.neg_add, &[b]);
        let body = trans(d, c, add_nbb, add_bnb, c.zero, comm_nb_b, na_b);
        d.lam_fv(b_fv, c.carrier, body)
    };

    let args = [
        c.carrier,
        c.equiv,
        c.erefl,
        c.esymm,
        c.etrans,
        c.add,
        c.add_congr,
        c.zero,
        c.neg,
        neg_congr,
        c.add_assoc,
        ident_l,
        c.add_zero,
        inv_l,
        c.neg_add,
    ];
    let value = {
        let k = d.kernel();
        mk_instance(k, group, &args)
    };
    let ord_ty = rec_ty(d, rn);
    let value = d.lam_fv(r_fv, ord_ty, value);
    let ty = {
        let dom = rec_ty(d, rn);
        let cod = rec_ty(d, group);
        d.arrow(dom, cod)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: names.to_group_s,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `equiv ((a+b)+(c+e)) ((a+c)+(b+e))` — the middle-four exchange.
///
/// `AlgS.add_add_add_comm` proves exactly this, but over `AlgS.CommRing`,
/// and `AlgS.OrderedRing` carries no `mulComm` so there is no projection to
/// a `CommRing` (ADR-1592 §2 built the record Ring-based on purpose). The
/// exchange uses only `addAssoc`/`addComm`/`addCongr`, all of which the
/// ordered ring has, so it is rebuilt here rather than reached.
#[allow(clippy::many_single_char_names)]
fn four_exchange(
    d: &mut IntDev<'_>,
    c: Rec,
    a: ExprId,
    b: ExprId,
    c2: ExprId,
    e: ExprId,
) -> ExprId {
    let ab = radd(d, c, a, b);
    let ce = radd(d, c, c2, e);
    let bc = radd(d, c, b, c2);
    let cb = radd(d, c, c2, b);
    let be = radd(d, c, b, e);
    let ac = radd(d, c, a, c2);
    let b_ce = radd(d, c, b, ce);
    let bc_e = radd(d, c, bc, e);
    let cb_e = radd(d, c, cb, e);
    let c_be = radd(d, c, c2, be);
    let lhs = radd(d, c, ab, ce);
    let a_bce = radd(d, c, a, b_ce);
    let a_cbe = radd(d, c, a, c_be);
    let rhs = radd(d, c, ac, be);

    // t1 : (a+b)+(c+e) ~ a+(b+(c+e))
    let t1 = d.apply(c.add_assoc, &[a, b, ce]);
    // inner : b+(c+e) ~ c+(b+e)
    let i1 = {
        let assoc = d.apply(c.add_assoc, &[b, c2, e]); // (b+c)+e ~ b+(c+e)
        symm(d, c, bc_e, b_ce, assoc)
    };
    let i2 = {
        let comm = d.apply(c.add_comm, &[b, c2]);
        let refl_e = refl(d, c, e);
        acongr(d, c, bc, cb, e, e, comm, refl_e)
    };
    let i3 = d.apply(c.add_assoc, &[c2, b, e]); // (c+b)+e ~ c+(b+e)
    let i12 = trans(d, c, b_ce, bc_e, cb_e, i1, i2);
    let inner = trans(d, c, b_ce, cb_e, c_be, i12, i3);
    // t2 : a+(b+(c+e)) ~ a+(c+(b+e))
    let refl_a = refl(d, c, a);
    let t2 = acongr(d, c, a, a, b_ce, c_be, refl_a, inner);
    // t3 : a+(c+(b+e)) ~ (a+c)+(b+e)
    let assoc3 = d.apply(c.add_assoc, &[a, c2, be]); // (a+c)+(b+e) ~ a+(c+(b+e))
    let t3 = symm(d, c, rhs, a_cbe, assoc3);
    let s12 = trans(d, c, lhs, a_bce, a_cbe, t1, t2);
    trans(d, c, lhs, a_cbe, rhs, s12, t3)
}

// ---------------------------------------------------------------------------
// `AlgS.OrderedRing.sumRange` and its two defining equations.
// ---------------------------------------------------------------------------

/// `AlgS.OrderedRing.sumRange : ∀ (R : OrderedRing), (Nat → R.carrier) → Nat
/// → R.carrier`, with `sumRange R f 0 ≡ R.zero` and `sumRange R f (succ j) ≡
/// R.add (sumRange R f j) (f j)`.
///
/// The SAME `Nat.rec` shape `Rat.sumRange` and `CReal.sumRange` each have,
/// with the carrier's `zero`/`add` read off the record instead of named. At
/// `R := AlgS.Rat.orderedRingS` the two projections δ-reduce to `Rat.zero`
/// and `Rat.add`, so this constant and `Rat.sumRange` are definitionally
/// equal — which is what makes every theorem below an instance rather than
/// an analogue.
fn declare_sum_range(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let l1 = d.level_one();

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d
        .kernel()
        .lam(anon, nat, c.carrier, crate::BinderInfo::Default);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = radd(d, c, ih, fj);
        let inner = d.lam_fv(ih_fv, c.carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![l1]);
    let body = d.apply(rec, &[motive, c.zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_f = d.lam_fv(f_fv, fn_ty, with_n);
        let ord_ty = rec_ty(d, rn);
        d.lam_fv(r_fv, ord_ty, with_f)
    };
    let ty = {
        let over_n = d.arrow(nat, c.carrier);
        let over_f = d.arrow(fn_ty, over_n);
        let ord_ty = rec_ty(d, rn);
        d.pi_fv(r_fv, ord_ty, over_f)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: names.sum_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })
}

/// `AlgS.OrderedRing.sumRange_zero` / `sumRange_succ`: the defining
/// equations, each closed by the record's own `equivRefl` since the `Nat.rec`
/// application ι-reduces on both minor premises.
fn declare_sum_range_equations(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let c = proj(d, rn, r);
        let fn_ty = d.arrow(nat, c.carrier);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = sum_range_of(d, names, r, f, zero_n);
        let stmt = eqv(d, c, lhs, c.zero);
        let proof = refl(d, c, c.zero);
        let ord_ty = rec_ty(d, rn);
        let ty = {
            let over_f = d.pi_fv(f_fv, fn_ty, stmt);
            d.pi_fv(r_fv, ord_ty, over_f)
        };
        let value = {
            let over_f = d.lam_fv(f_fv, fn_ty, proof);
            d.lam_fv(r_fv, ord_ty, over_f)
        };
        d.declare_theorem(names.sum_range_zero, ty, value)?;
    }
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let c = proj(d, rn, r);
        let fn_ty = d.arrow(nat, c.carrier);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = sum_range_of(d, names, r, f, sn);
        let prior = sum_range_of(d, names, r, f, n);
        let fn_at = d.apply(f, &[n]);
        let rhs = radd(d, c, prior, fn_at);
        let stmt = eqv(d, c, lhs, rhs);
        let proof = refl(d, c, rhs);
        let ord_ty = rec_ty(d, rn);
        let ty = {
            let over_n = d.pi_fv(n_fv, nat, stmt);
            let over_f = d.pi_fv(f_fv, fn_ty, over_n);
            d.pi_fv(r_fv, ord_ty, over_f)
        };
        let value = {
            let over_n = d.lam_fv(n_fv, nat, proof);
            let over_f = d.lam_fv(f_fv, fn_ty, over_n);
            d.lam_fv(r_fv, ord_ty, over_f)
        };
        d.declare_theorem(names.sum_range_succ, ty, value)?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The sum laws expectation's linearity is built from.
// ---------------------------------------------------------------------------

/// `AlgS.OrderedRing.sumRange_congr : ∀ R f g n, (∀ k, k < n → equiv (f k)
/// (g k)) → equiv (sumRange R f n) (sumRange R g n)`.
///
/// The congruence a setoid must carry by hand. On the `Eq`-flavored side a
/// pointwise equality can be `funext`-ed and the two sums are then literally
/// the same term; here `equiv` is an arbitrary relation, so the sum has to
/// be rebuilt by induction with `addCongr` at every step. This is the
/// concrete price of ADR-1588's setoid choice inside the probability layer,
/// and it is one theorem, paid once.
fn declare_sum_range_congr(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let bounded_eqv = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hyp = d.lt(i, bound);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body_eq = eqv(d, c, fi, gi);
        let body = d.arrow(hyp, body_eq);
        d.pi_fv(i_fv, nat, body)
    };
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_eqv(d, x);
        let lhs = sum_range_of(d, names, r, f, x);
        let rhs = sum_range_of(d, names, r, g, x);
        let concl = eqv(d, c, lhs, rhs);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_eqv(d, zero_n);
            let h_fv = d.fresh_fvar();
            let body = refl(d, c, c.zero);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_eqv(d, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let (below, at_j) = restrict(d, h, j, sj);
            let sub1 = d.apply(ih, &[below]);
            let sf = sum_range_of(d, names, r, f, j);
            let sg = sum_range_of(d, names, r, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let body = acongr(d, c, sf, sg, fj, gj, sub1, at_j);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        let over_f = d.pi_fv(f_fv, fn_ty, over_g);
        d.pi_fv(r_fv, ord_ty, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        let over_f = d.lam_fv(f_fv, fn_ty, over_g);
        d.lam_fv(r_fv, ord_ty, over_f)
    };
    d.declare_theorem(names.sum_range_congr, ty, value)
}

/// `AlgS.OrderedRing.sumRange_add : ∀ R f g n, equiv (sumRange R (fun k =>
/// f k + g k) n) (add (sumRange R f n) (sumRange R g n))`.
///
/// Induction on `n`. The base case is `equiv zero (add zero zero)`, i.e.
/// `equivSymm (addZero zero)`; the successor step is exactly the four-term
/// rearrangement `AlgS.add_add_add_comm` already proves over `AlgS.Ring`,
/// reached here through [`declare_to_ring_s`].
fn declare_sum_range_add(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fg = combined(d, c, f, g);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = sum_range_of(d, names, r, fg, x);
        let sf = sum_range_of(d, names, r, f, x);
        let sg = sum_range_of(d, names, r, g, x);
        let rhs = radd(d, c, sf, sg);
        eqv(d, c, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zz = radd(d, c, c.zero, c.zero);
            let h = d.apply(c.add_zero, &[c.zero]);
            symm(d, c, zz, c.zero, h)
        },
        &|d, j, ih| {
            let sf = sum_range_of(d, names, r, f, j);
            let sg = sum_range_of(d, names, r, g, j);
            let sfg = sum_range_of(d, names, r, fg, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let fgj = radd(d, c, fj, gj);
            let sum_sfg = radd(d, c, sf, sg);
            // step1 : equiv (add sfg fgj) (add (add sf sg) fgj)
            let refl_fgj = refl(d, c, fgj);
            let step1 = acongr(d, c, sfg, sum_sfg, fgj, fgj, ih, refl_fgj);
            // step2 : equiv (add (add sf sg) (add fj gj))
            //               (add (add sf fj) (add sg gj))
            let step2 = four_exchange(d, c, sf, sg, fj, gj);
            let lhs = radd(d, c, sfg, fgj);
            let mid = radd(d, c, sum_sfg, fgj);
            let sf_fj = radd(d, c, sf, fj);
            let sg_gj = radd(d, c, sg, gj);
            let rhs = radd(d, c, sf_fj, sg_gj);
            trans(d, c, lhs, mid, rhs, step1, step2)
        },
        n,
    );

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        let over_f = d.pi_fv(f_fv, fn_ty, over_g);
        d.pi_fv(r_fv, ord_ty, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        let over_f = d.lam_fv(f_fv, fn_ty, over_g);
        d.lam_fv(r_fv, ord_ty, over_f)
    };
    d.declare_theorem(names.sum_range_add, ty, value)
}

/// `AlgS.OrderedRing.mul_sumRange : ∀ R a f n, equiv (sumRange R (fun k =>
/// a * f k) n) (mul a (sumRange R f n))`.
///
/// Induction on `n`, with `AlgS.mul_zero` closing the base case and the
/// record's own `distribL` the step.
fn declare_mul_sum_range(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
    algs_mul_zero: NameId,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let ring_r = d.const_app(names.to_ring_s, &[r]);
    let fn_ty = d.arrow(nat, c.carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let af = scaled(d, c, a, f);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = sum_range_of(d, names, r, af, x);
        let sf = sum_range_of(d, names, r, f, x);
        let rhs = rmul(d, c, a, sf);
        eqv(d, c, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let az = rmul(d, c, a, c.zero);
            let h = d.const_app(algs_mul_zero, &[ring_r, a]);
            symm(d, c, az, c.zero, h)
        },
        &|d, j, ih| {
            let saf = sum_range_of(d, names, r, af, j);
            let sf = sum_range_of(d, names, r, f, j);
            let fj = d.apply(f, &[j]);
            let afj = rmul(d, c, a, fj);
            let a_sf = rmul(d, c, a, sf);
            // step1 : equiv (add saf afj) (add (mul a sf) afj)
            let refl_afj = refl(d, c, afj);
            let step1 = acongr(d, c, saf, a_sf, afj, afj, ih, refl_afj);
            // step2 : equiv (mul a (add sf fj)) (add (mul a sf) (mul a fj))
            let dl = d.apply(c.distrib_l, &[a, sf, fj]);
            let sf_fj = radd(d, c, sf, fj);
            let a_sf_fj = rmul(d, c, a, sf_fj);
            let sum_parts = radd(d, c, a_sf, afj);
            let step2 = symm(d, c, a_sf_fj, sum_parts, dl);
            let lhs = radd(d, c, saf, afj);
            trans(d, c, lhs, sum_parts, a_sf_fj, step1, step2)
        },
        n,
    );

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_f = d.pi_fv(f_fv, fn_ty, over_n);
        let over_a = d.pi_fv(a_fv, c.carrier, over_f);
        d.pi_fv(r_fv, ord_ty, over_a)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_f = d.lam_fv(f_fv, fn_ty, over_n);
        let over_a = d.lam_fv(a_fv, c.carrier, over_f);
        d.lam_fv(r_fv, ord_ty, over_a)
    };
    d.declare_theorem(names.mul_sum_range, ty, value)
}

// ---------------------------------------------------------------------------
// The two order laws every probability bound is built from.
// ---------------------------------------------------------------------------

/// `add_le_add` at the record, i.e. `le a b → le c e → le (add a c) (add b
/// e)` — ADR-1592 already declared it as `AlgS.OrderedRing.add_le_add`, so
/// this is just the application spelled once.
#[allow(clippy::too_many_arguments)]
fn add_le_add(
    d: &mut IntDev<'_>,
    add_le_add_name: NameId,
    r: ExprId,
    a: ExprId,
    b: ExprId,
    c2: ExprId,
    e: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    d.const_app(add_le_add_name, &[r, a, b, c2, e, h1, h2])
}

/// `AlgS.OrderedRing.sumRange_le : ∀ R f g n, (∀ i, i < n → le (f i) (g i))
/// → le (sumRange R f n) (sumRange R g n)` — monotonicity.
fn declare_sum_range_le(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
    add_le_add_name: NameId,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_le(d, c, f, g, x);
        let lhs = sum_range_of(d, names, r, f, x);
        let rhs = sum_range_of(d, names, r, g, x);
        let concl = rle(d, c, lhs, rhs);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_le(d, c, f, g, zero_n);
            let h_fv = d.fresh_fvar();
            let body = d.apply(c.le_refl, &[c.zero]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_le(d, c, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let (below, at_j) = restrict(d, h, j, sj);
            let sub1 = d.apply(ih, &[below]);
            let sf = sum_range_of(d, names, r, f, j);
            let sg = sum_range_of(d, names, r, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let body = add_le_add(d, add_le_add_name, r, sf, sg, fj, gj, sub1, at_j);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        let over_f = d.pi_fv(f_fv, fn_ty, over_g);
        d.pi_fv(r_fv, ord_ty, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        let over_f = d.lam_fv(f_fv, fn_ty, over_g);
        d.lam_fv(r_fv, ord_ty, over_f)
    };
    d.declare_theorem(names.sum_range_le, ty, value)
}

/// `AlgS.OrderedRing.sumRange_nonneg : ∀ R f n, (∀ i, i < n → le zero (f i))
/// → le zero (sumRange R f n)`.
fn declare_sum_range_nonneg(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
    add_le_add_name: NameId,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_nonneg(d, c, f, x);
        let sum = sum_range_of(d, names, r, f, x);
        let concl = rle(d, c, c.zero, sum);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_nonneg(d, c, f, zero_n);
            let h_fv = d.fresh_fvar();
            let body = d.apply(c.le_refl, &[c.zero]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_nonneg(d, c, f, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let (below, at_j) = restrict(d, h, j, sj);
            let sub1 = d.apply(ih, &[below]);
            let sf = sum_range_of(d, names, r, f, j);
            let fj = d.apply(f, &[j]);
            // le (add zero zero) (add sf fj), then rewrite the left side.
            let raw = add_le_add(d, add_le_add_name, r, c.zero, sf, c.zero, fj, sub1, at_j);
            let zz = radd(d, c, c.zero, c.zero);
            let hz = d.apply(c.add_zero, &[c.zero]);
            let rhs = radd(d, c, sf, fj);
            let refl_rhs = refl(d, c, rhs);
            let body = lecongr(d, c, zz, c.zero, rhs, rhs, hz, refl_rhs, raw);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_f = d.pi_fv(f_fv, fn_ty, over_n);
        d.pi_fv(r_fv, ord_ty, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_f = d.lam_fv(f_fv, fn_ty, over_n);
        d.lam_fv(r_fv, ord_ty, over_f)
    };
    d.declare_theorem(names.sum_range_nonneg, ty, value)
}

// ---------------------------------------------------------------------------
// The price of `mul_le_mul_of_nonneg_right`.
// ---------------------------------------------------------------------------

/// `AlgS.OrderedRing.zero_mul : ∀ R a, equiv (mul zero a) zero`.
///
/// `AlgS.mul_zero` (the `a * 0` side) is on the spine; the `0 * a` side is
/// not, and without `mulComm` — which `AlgS.OrderedRing` deliberately does
/// not carry (ADR-1592 §2) — it does not follow from it. Proved instead by
/// `x + x ≃ x → x ≃ zero`: `distribR zero zero a` gives `(0+0)*a ≃ 0*a +
/// 0*a`, and `addZero`/`addCongr` turn the left side into `0*a`, so
/// `AlgS.add_left_cancel` at `0*a` against `addZero (0*a)` closes it.
fn declare_zero_mul(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
    add_left_cancel: NameId,
) -> Result<(), KernelError> {
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let group_r = d.const_app(names.to_group_s, &[r]);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let x = rmul(d, c, c.zero, a); // x := 0 * a
    let zz = radd(d, c, c.zero, c.zero);
    let zz_a = rmul(d, c, zz, a);
    let x_x = radd(d, c, x, x);

    // h1 : equiv ((0+0)*a) (0*a + 0*a)   [distribR]
    let h1 = d.apply(c.distrib_r, &[c.zero, c.zero, a]);
    // h2 : equiv ((0+0)*a) (0*a)         [addZero 0, mulCongr]
    let hz = d.apply(c.add_zero, &[c.zero]);
    let refl_a = refl(d, c, a);
    let h2 = mcongr(d, c, zz, c.zero, a, a, hz, refl_a);
    // h3 : equiv (0*a) (0*a + 0*a)
    let h2s = symm(d, c, zz_a, x, h2);
    let h3 = trans(d, c, x, zz_a, x_x, h2s, h1);
    // h4 : equiv (0*a + 0) (0*a)         [addZero]
    let h4 = d.apply(c.add_zero, &[x]);
    let x_zero = radd(d, c, x, c.zero);
    // h5 : equiv (0*a + 0) (0*a + 0*a)
    let h5 = trans(d, c, x_zero, x, x_x, h4, h3);
    // add_left_cancel R (0*a) 0 (0*a) h5 : equiv 0 (0*a)
    let cancel = d.const_app(add_left_cancel, &[group_r, x, c.zero, x, h5]);
    let value_core = symm(d, c, c.zero, x, cancel);

    let stmt = eqv(d, c, x, c.zero);
    let ord_ty = rec_ty(d, rn);
    let ty = {
        let over_a = d.pi_fv(a_fv, c.carrier, stmt);
        d.pi_fv(r_fv, ord_ty, over_a)
    };
    let value = {
        let over_a = d.lam_fv(a_fv, c.carrier, value_core);
        d.lam_fv(r_fv, ord_ty, over_a)
    };
    d.declare_theorem(names.zero_mul, ty, value)
}

/// `AlgS.OrderedRing.neg_mul : ∀ R a b, equiv (mul (neg a) b) (neg (mul a
/// b))`.
///
/// Both sides are additive inverses of `a * b`: `a*b + (-a)*b ≃ (a + -a)*b ≃
/// 0*b ≃ 0` (by `distribR`, `negAdd` and [`declare_zero_mul`]) and `a*b +
/// -(a*b) ≃ 0` (by `negAdd`), so `AlgS.add_left_cancel` at `a*b` finishes.
fn declare_neg_mul(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
    add_left_cancel: NameId,
) -> Result<(), KernelError> {
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let group_r = d.const_app(names.to_group_s, &[r]);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let na = rneg(d, c, a);
    let ab = rmul(d, c, a, b);
    let nab = rmul(d, c, na, b);
    let n_ab = rneg(d, c, ab);
    let sum_l = radd(d, c, ab, nab);
    let sum_r = radd(d, c, ab, n_ab);
    let a_na = radd(d, c, a, na);
    let a_na_b = rmul(d, c, a_na, b);
    let zero_b = rmul(d, c, c.zero, b);

    // l1 : equiv ((a + -a)*b) (a*b + (-a)*b)  [distribR]
    let l1 = d.apply(c.distrib_r, &[a, na, b]);
    // l2 : equiv (a*b + (-a)*b) ((a + -a)*b)
    let l2 = symm(d, c, a_na_b, sum_l, l1);
    // l3 : equiv ((a + -a)*b) (0*b)  [negAdd a, mulCongr]
    let hna = d.apply(c.neg_add, &[a]);
    let refl_b = refl(d, c, b);
    let l3 = mcongr(d, c, a_na, c.zero, b, b, hna, refl_b);
    // l4 : equiv (0*b) 0
    let l4 = d.const_app(names.zero_mul, &[r, b]);
    // left : equiv (a*b + (-a)*b) 0
    let l23 = trans(d, c, sum_l, a_na_b, zero_b, l2, l3);
    let left = trans(d, c, sum_l, zero_b, c.zero, l23, l4);
    // right : equiv (a*b + -(a*b)) 0
    let right = d.apply(c.neg_add, &[ab]);
    // h : equiv (a*b + (-a)*b) (a*b + -(a*b))
    let right_s = symm(d, c, sum_r, c.zero, right);
    let h = trans(d, c, sum_l, c.zero, sum_r, left, right_s);
    let value_core = d.const_app(add_left_cancel, &[group_r, ab, nab, n_ab, h]);

    let stmt = eqv(d, c, nab, n_ab);
    let ord_ty = rec_ty(d, rn);
    let ty = {
        let over_b = d.pi_fv(b_fv, c.carrier, stmt);
        let over_a = d.pi_fv(a_fv, c.carrier, over_b);
        d.pi_fv(r_fv, ord_ty, over_a)
    };
    let value = {
        let over_b = d.lam_fv(b_fv, c.carrier, value_core);
        let over_a = d.lam_fv(a_fv, c.carrier, over_b);
        d.lam_fv(r_fv, ord_ty, over_a)
    };
    d.declare_theorem(names.neg_mul, ty, value)
}

/// `AlgS.OrderedRing.sub_nonneg_of_le : ∀ R a b, le a b → le zero (add b
/// (neg a))`.
///
/// `add_le_add_right` (ADR-1592) at `neg a`, with `negAdd a` rewriting the
/// left side from `a + -a` to `zero` through `leCongr`.
fn declare_sub_nonneg_of_le(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
    add_le_add_right: NameId,
) -> Result<(), KernelError> {
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hyp_ty = rle(d, c, a, b);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let na = rneg(d, c, a);
    let a_na = radd(d, c, a, na);
    let b_na = radd(d, c, b, na);
    let raw = d.const_app(add_le_add_right, &[r, a, b, na, h]); // le (a + -a) (b + -a)
    let hna = d.apply(c.neg_add, &[a]);
    let refl_bna = refl(d, c, b_na);
    let core = lecongr(d, c, a_na, c.zero, b_na, b_na, hna, refl_bna, raw);

    let concl = rle(d, c, c.zero, b_na);
    let ord_ty = rec_ty(d, rn);
    let ty = {
        let t = d.arrow(hyp_ty, concl);
        let over_b = d.pi_fv(b_fv, c.carrier, t);
        let over_a = d.pi_fv(a_fv, c.carrier, over_b);
        d.pi_fv(r_fv, ord_ty, over_a)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, core);
        let over_b = d.lam_fv(b_fv, c.carrier, t);
        let over_a = d.lam_fv(a_fv, c.carrier, over_b);
        d.lam_fv(r_fv, ord_ty, over_a)
    };
    d.declare_theorem(names.sub_nonneg_of_le, ty, value)
}

/// `AlgS.OrderedRing.mul_le_mul_of_nonneg_right : ∀ R a b e, le a b → le
/// zero e → le (mul a e) (mul b e)`.
///
/// The workhorse the `ℚ` development has as a primitive. Here:
/// `sub_nonneg_of_le` then `mul_nonneg` give `0 ≤ (b + -a) * e`; `distribR`
/// and [`declare_neg_mul`] rewrite that to `0 ≤ b*e + -(a*e)`;
/// `add_le_add_left` at `a*e` and two `addZero`/`addAssoc`/`negAdd` rewrites
/// finish.
#[allow(clippy::too_many_lines)]
fn declare_mul_le_mul_of_nonneg_right(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let he_ty = rle(d, c, c.zero, e);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);

    let na = rneg(d, c, a);
    let b_na = radd(d, c, b, na);
    let ae = rmul(d, c, a, e);
    let be = rmul(d, c, b, e);
    let nae = rmul(d, c, na, e);
    let n_ae = rneg(d, c, ae);
    let bna_e = rmul(d, c, b_na, e);

    // h0 : le zero ((b + -a) * e)
    let hsub = d.const_app(names.sub_nonneg_of_le, &[r, a, b, hab]);
    let h0 = d.apply(c.mul_nonneg, &[b_na, e, hsub, he]);
    // h1 : equiv ((b + -a)*e) (b*e + (-a)*e)  [distribR]
    let h1 = d.apply(c.distrib_r, &[b, na, e]);
    // h2 : equiv (b*e + (-a)*e) (b*e + -(a*e))  [neg_mul, addCongr]
    let hnm = d.const_app(names.neg_mul, &[r, a, e]);
    let refl_be = refl(d, c, be);
    let h2 = acongr(d, c, be, be, nae, n_ae, refl_be, hnm);
    let sum1 = radd(d, c, be, nae);
    let sum2 = radd(d, c, be, n_ae);
    let h12 = trans(d, c, bna_e, sum1, sum2, h1, h2);
    // h3 : le zero (b*e + -(a*e))
    let refl_zero = refl(d, c, c.zero);
    let h3 = lecongr(d, c, c.zero, c.zero, bna_e, sum2, refl_zero, h12, h0);
    // h4 : le (a*e + zero) (a*e + (b*e + -(a*e)))
    let h4 = d.apply(c.add_le_add_left, &[c.zero, sum2, ae, h3]);
    // left : equiv (a*e + zero) (a*e)
    let left = d.apply(c.add_zero, &[ae]);
    let ae_zero = radd(d, c, ae, c.zero);
    // right : equiv (a*e + (b*e + -(a*e))) (b*e)
    //   a*e + (b*e + -(a*e)) ~ (a*e + b*e) + -(a*e)      [symm addAssoc]
    //                        ~ (b*e + a*e) + -(a*e)      [addComm, addCongr]
    //                        ~ b*e + (a*e + -(a*e))      [addAssoc]
    //                        ~ b*e + zero                [negAdd, addCongr]
    //                        ~ b*e                       [addZero]
    let ae_sum2 = radd(d, c, ae, sum2);
    let ae_be = radd(d, c, ae, be);
    let be_ae = radd(d, c, be, ae);
    let ae_be_nae = radd(d, c, ae_be, n_ae);
    let be_ae_nae = radd(d, c, be_ae, n_ae);
    let ae_nae = radd(d, c, ae, n_ae);
    let be_zero = radd(d, c, be, c.zero);
    let assoc1 = d.apply(c.add_assoc, &[ae, be, n_ae]); // (ae+be)+nae ~ ae+(be+nae)
    let s1 = symm(d, c, ae_be_nae, ae_sum2, assoc1);
    let comm1 = d.apply(c.add_comm, &[ae, be]);
    let refl_nae = refl(d, c, n_ae);
    let s2 = acongr(d, c, ae_be, be_ae, n_ae, n_ae, comm1, refl_nae);
    let assoc2 = d.apply(c.add_assoc, &[be, ae, n_ae]); // (be+ae)+nae ~ be+(ae+nae)
    let hnegadd = d.apply(c.neg_add, &[ae]);
    let s4 = acongr(d, c, be, be, ae_nae, c.zero, refl_be, hnegadd);
    let be_ae_nae_r = radd(d, c, be, ae_nae);
    let s5 = d.apply(c.add_zero, &[be]);
    let c1 = trans(d, c, ae_sum2, ae_be_nae, be_ae_nae, s1, s2);
    let c2 = trans(d, c, ae_sum2, be_ae_nae, be_ae_nae_r, c1, assoc2);
    let c3 = trans(d, c, ae_sum2, be_ae_nae_r, be_zero, c2, s4);
    let right = trans(d, c, ae_sum2, be_zero, be, c3, s5);
    let core = lecongr(d, c, ae_zero, ae, ae_sum2, be, left, right, h4);

    let concl = rle(d, c, ae, be);
    let ord_ty = rec_ty(d, rn);
    let ty = {
        let t = d.arrow(he_ty, concl);
        let t = d.arrow(hab_ty, t);
        let over_e = d.pi_fv(e_fv, c.carrier, t);
        let over_b = d.pi_fv(b_fv, c.carrier, over_e);
        let over_a = d.pi_fv(a_fv, c.carrier, over_b);
        d.pi_fv(r_fv, ord_ty, over_a)
    };
    let value = {
        let t = d.lam_fv(he_fv, he_ty, core);
        let t = d.lam_fv(hab_fv, hab_ty, t);
        let over_e = d.lam_fv(e_fv, c.carrier, t);
        let over_b = d.lam_fv(b_fv, c.carrier, over_e);
        let over_a = d.lam_fv(a_fv, c.carrier, over_b);
        d.lam_fv(r_fv, ord_ty, over_a)
    };
    d.declare_theorem(names.mul_le_mul_of_nonneg_right, ty, value)
}

// ---------------------------------------------------------------------------
// `IsDistribution`, `expectation`, and expectation's four laws.
// ---------------------------------------------------------------------------

/// `AlgS.OrderedRing.IsDistribution R p n := (∀ k, k < n → le zero (p k)) ∧
/// equiv (sumRange R p n) one`.
fn declare_is_distribution(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let anon = d.anon_name();

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let nonneg_part = bounded_nonneg(d, c, pf, n);
    let sum_part = {
        let sum = sum_range_of(d, names, r, pf, n);
        eqv(d, c, sum, c.one)
    };
    let body = d.and(nonneg_part, sum_part);
    let value = {
        let inner = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        let ord_ty = rec_ty(d, rn);
        d.lam_fv(r_fv, ord_ty, with_pf)
    };
    let ty = {
        let inner = d.kernel().pi(anon, nat, prop, crate::BinderInfo::Default);
        let with_pf = d.arrow(fn_ty, inner);
        let ord_ty = rec_ty(d, rn);
        d.pi_fv(r_fv, ord_ty, with_pf)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: names.is_distribution,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(3),
    })
}

/// `AlgS.OrderedRing.IsDistribution R p n`, and its two components rebuilt
/// so a caller can project through `And.rec`.
fn is_distribution_parts(
    d: &mut IntDev<'_>,
    c: Rec,
    names: &ProbSNames,
    r: ExprId,
    pf: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let nonneg_part = bounded_nonneg(d, c, pf, n);
    let sum_part = {
        let sum = sum_range_of(d, names, r, pf, n);
        eqv(d, c, sum, c.one)
    };
    (nonneg_part, sum_part)
}

/// `AlgS.OrderedRing.expectation R X p n := sumRange R (fun k => X k * p k)
/// n` — the SAME normalized weighted sum `Rat.expectation` is.
fn declare_expectation(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let summand = weighted(d, c, x, pf);
    let body = sum_range_of(d, names, r, summand, n);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_x = d.lam_fv(x_fv, fn_ty, with_pf);
        let ord_ty = rec_ty(d, rn);
        d.lam_fv(r_fv, ord_ty, with_x)
    };
    let ty = {
        let inner = d.arrow(nat, c.carrier);
        let over_pf = d.arrow(fn_ty, inner);
        let over_x = d.arrow(fn_ty, over_pf);
        let ord_ty = rec_ty(d, rn);
        d.pi_fv(r_fv, ord_ty, over_x)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: names.expectation,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(4),
    })
}

/// `AlgS.OrderedRing.expectation_add : ∀ R X Y p n, equiv (expectation R
/// (fun k => X k + Y k) p n) (add (expectation R X p n) (expectation R Y p
/// n))`.
///
/// `distribR` pointwise turns the combined weighted summand into a sum of
/// two, and [`declare_sum_range_add`] splits it. The pointwise step needs a
/// congruence UNDER the binder, which a setoid does not get for free — so it
/// is done by proving the two summand functions equal as `Nat → carrier`
/// terms is NOT available, and instead `sumRange_congr` is used.
fn declare_expectation_add(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xy = combined(d, c, x, y);
    let w_xy = weighted(d, c, xy, pf);
    let w_x = weighted(d, c, x, pf);
    let w_y = weighted(d, c, y, pf);
    let split = combined(d, c, w_x, w_y);

    // h1 : equiv (sumRange w_xy n) (sumRange split n)  -- pointwise distribR
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(kv, n);
        let hk_fv = d.fresh_fvar();
        let xk = d.apply(x, &[kv]);
        let yk = d.apply(y, &[kv]);
        let pk = d.apply(pf, &[kv]);
        let body = d.apply(c.distrib_r, &[xk, yk, pk]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let h1 = d.const_app(names.sum_range_congr, &[r, w_xy, split, n, pointwise]);
    // h2 : equiv (sumRange split n) (add (sumRange w_x n) (sumRange w_y n))
    let h2 = d.const_app(names.sum_range_add, &[r, w_x, w_y, n]);

    let lhs = expectation_of(d, names, r, xy, pf, n);
    let mid = sum_range_of(d, names, r, split, n);
    let ex = expectation_of(d, names, r, x, pf, n);
    let ey = expectation_of(d, names, r, y, pf, n);
    let rhs = radd(d, c, ex, ey);
    let core = trans(d, c, lhs, mid, rhs, h1, h2);
    let stmt = eqv(d, c, lhs, rhs);

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_pf = d.pi_fv(pf_fv, fn_ty, over_n);
        let over_y = d.pi_fv(y_fv, fn_ty, over_pf);
        let over_x = d.pi_fv(x_fv, fn_ty, over_y);
        d.pi_fv(r_fv, ord_ty, over_x)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, core);
        let over_pf = d.lam_fv(pf_fv, fn_ty, over_n);
        let over_y = d.lam_fv(y_fv, fn_ty, over_pf);
        let over_x = d.lam_fv(x_fv, fn_ty, over_y);
        d.lam_fv(r_fv, ord_ty, over_x)
    };
    d.declare_theorem(names.expectation_add, ty, value)
}

/// `AlgS.OrderedRing.expectation_smul : ∀ R a X p n, equiv (expectation R
/// (fun k => a * X k) p n) (mul a (expectation R X p n))`.
fn declare_expectation_smul(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let ax = scaled(d, c, a, x);
    let w_ax = weighted(d, c, ax, pf);
    let w_x = weighted(d, c, x, pf);
    let a_wx = scaled(d, c, a, w_x);

    // pointwise : (a * X k) * p k ≃ a * (X k * p k)   [mulAssoc]
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(kv, n);
        let hk_fv = d.fresh_fvar();
        let xk = d.apply(x, &[kv]);
        let pk = d.apply(pf, &[kv]);
        let body = d.apply(c.mul_assoc, &[a, xk, pk]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let h1 = d.const_app(names.sum_range_congr, &[r, w_ax, a_wx, n, pointwise]);
    let h2 = d.const_app(names.mul_sum_range, &[r, a, w_x, n]);

    let lhs = expectation_of(d, names, r, ax, pf, n);
    let mid = sum_range_of(d, names, r, a_wx, n);
    let ex = expectation_of(d, names, r, x, pf, n);
    let rhs = rmul(d, c, a, ex);
    let core = trans(d, c, lhs, mid, rhs, h1, h2);
    let stmt = eqv(d, c, lhs, rhs);

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_pf = d.pi_fv(pf_fv, fn_ty, over_n);
        let over_x = d.pi_fv(x_fv, fn_ty, over_pf);
        let over_a = d.pi_fv(a_fv, c.carrier, over_x);
        d.pi_fv(r_fv, ord_ty, over_a)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, core);
        let over_pf = d.lam_fv(pf_fv, fn_ty, over_n);
        let over_x = d.lam_fv(x_fv, fn_ty, over_pf);
        let over_a = d.lam_fv(a_fv, c.carrier, over_x);
        d.lam_fv(r_fv, ord_ty, over_a)
    };
    d.declare_theorem(names.expectation_smul, ty, value)
}

/// `AlgS.OrderedRing.expectation_const : ∀ R c0 p n, IsDistribution R p n →
/// equiv (expectation R (fun _ => c0) p n) c0`.
fn declare_expectation_const(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let c0_fv = d.fresh_fvar();
    let c0 = d.kernel().fvar(c0_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let const_x = {
        let k_fv = d.fresh_fvar();
        d.lam_fv(k_fv, nat, c0)
    };
    let hyp_ty = d.const_app(names.is_distribution, &[r, pf, n]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let (left_part, right_part) = is_distribution_parts(d, c, names, r, pf, n);
    let hsum = d.and_right(left_part, right_part, h);

    // expectation R (fun _ => c0) p n = sumRange R (fun k => c0 * p k) n
    //   ≃ c0 * sumRange R p n     [mul_sumRange]
    //   ≃ c0 * one                [mulCongr, hsum]
    //   ≃ c0                      [mulOneR]
    let h1 = d.const_app(names.mul_sum_range, &[r, c0, pf, n]);
    let sp = sum_range_of(d, names, r, pf, n);
    let c0_sp = rmul(d, c, c0, sp);
    let c0_one = rmul(d, c, c0, c.one);
    let refl_c0 = refl(d, c, c0);
    let h2 = mcongr(d, c, c0, c0, sp, c.one, refl_c0, hsum);
    let h3 = d.apply(c.mul_one_r, &[c0]);
    let lhs = expectation_of(d, names, r, const_x, pf, n);
    let step12 = trans(d, c, lhs, c0_sp, c0_one, h1, h2);
    let core = trans(d, c, lhs, c0_one, c0, step12, h3);
    let stmt = eqv(d, c, lhs, c0);

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let t = d.arrow(hyp_ty, stmt);
        let over_n = d.pi_fv(n_fv, nat, t);
        let over_pf = d.pi_fv(pf_fv, fn_ty, over_n);
        let over_c0 = d.pi_fv(c0_fv, c.carrier, over_pf);
        d.pi_fv(r_fv, ord_ty, over_c0)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, core);
        let over_n = d.lam_fv(n_fv, nat, t);
        let over_pf = d.lam_fv(pf_fv, fn_ty, over_n);
        let over_c0 = d.lam_fv(c0_fv, c.carrier, over_pf);
        d.lam_fv(r_fv, ord_ty, over_c0)
    };
    d.declare_theorem(names.expectation_const, ty, value)
}

/// `AlgS.OrderedRing.expectation_nonneg : ∀ R X p n, (∀ k, k < n → le zero
/// (X k)) → IsDistribution R p n → le zero (expectation R X p n)`.
fn declare_expectation_nonneg(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hx_ty = bounded_nonneg(d, c, x, n);
    let hx_fv = d.fresh_fvar();
    let hx = d.kernel().fvar(hx_fv);
    let hd_ty = d.const_app(names.is_distribution, &[r, pf, n]);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let (left_part, right_part) = is_distribution_parts(d, c, names, r, pf, n);
    let hp = d.and_left(left_part, right_part, hd);

    let w = weighted(d, c, x, pf);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(kv, n);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let xk = d.apply(x, &[kv]);
        let pk = d.apply(pf, &[kv]);
        let hxk = d.apply(hx, &[kv, hk]);
        let hpk = d.apply(hp, &[kv, hk]);
        let body = d.apply(c.mul_nonneg, &[xk, pk, hxk, hpk]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let core = d.const_app(names.sum_range_nonneg, &[r, w, n, pointwise]);
    let ex = expectation_of(d, names, r, x, pf, n);
    let stmt = rle(d, c, c.zero, ex);

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let t = d.arrow(hd_ty, stmt);
        let t = d.arrow(hx_ty, t);
        let over_n = d.pi_fv(n_fv, nat, t);
        let over_pf = d.pi_fv(pf_fv, fn_ty, over_n);
        let over_x = d.pi_fv(x_fv, fn_ty, over_pf);
        d.pi_fv(r_fv, ord_ty, over_x)
    };
    let value = {
        let t = d.lam_fv(hd_fv, hd_ty, core);
        let t = d.lam_fv(hx_fv, hx_ty, t);
        let over_n = d.lam_fv(n_fv, nat, t);
        let over_pf = d.lam_fv(pf_fv, fn_ty, over_n);
        let over_x = d.lam_fv(x_fv, fn_ty, over_pf);
        d.lam_fv(r_fv, ord_ty, over_x)
    };
    d.declare_theorem(names.expectation_nonneg, ty, value)
}

/// `AlgS.OrderedRing.expectation_le : ∀ R X Y p n, (∀ k, k < n → le (X k) (Y
/// k)) → IsDistribution R p n → le (expectation R X p n) (expectation R Y p
/// n)` — monotonicity, and the first consumer of
/// [`declare_mul_le_mul_of_nonneg_right`].
fn declare_expectation_le(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hxy_ty = bounded_le(d, c, x, y, n);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);
    let hd_ty = d.const_app(names.is_distribution, &[r, pf, n]);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let (left_part, right_part) = is_distribution_parts(d, c, names, r, pf, n);
    let hp = d.and_left(left_part, right_part, hd);

    let wx = weighted(d, c, x, pf);
    let wy = weighted(d, c, y, pf);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(kv, n);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let xk = d.apply(x, &[kv]);
        let yk = d.apply(y, &[kv]);
        let pk = d.apply(pf, &[kv]);
        let hxyk = d.apply(hxy, &[kv, hk]);
        let hpk = d.apply(hp, &[kv, hk]);
        let body = d.const_app(
            names.mul_le_mul_of_nonneg_right,
            &[r, xk, yk, pk, hxyk, hpk],
        );
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let core = d.const_app(names.sum_range_le, &[r, wx, wy, n, pointwise]);
    let ex = expectation_of(d, names, r, x, pf, n);
    let ey = expectation_of(d, names, r, y, pf, n);
    let stmt = rle(d, c, ex, ey);

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let t = d.arrow(hd_ty, stmt);
        let t = d.arrow(hxy_ty, t);
        let over_n = d.pi_fv(n_fv, nat, t);
        let over_pf = d.pi_fv(pf_fv, fn_ty, over_n);
        let over_y = d.pi_fv(y_fv, fn_ty, over_pf);
        let over_x = d.pi_fv(x_fv, fn_ty, over_y);
        d.pi_fv(r_fv, ord_ty, over_x)
    };
    let value = {
        let t = d.lam_fv(hd_fv, hd_ty, core);
        let t = d.lam_fv(hxy_fv, hxy_ty, t);
        let over_n = d.lam_fv(n_fv, nat, t);
        let over_pf = d.lam_fv(pf_fv, fn_ty, over_n);
        let over_y = d.lam_fv(y_fv, fn_ty, over_pf);
        let over_x = d.lam_fv(x_fv, fn_ty, over_y);
        d.lam_fv(r_fv, ord_ty, over_x)
    };
    d.declare_theorem(names.expectation_le, ty, value)
}

/// `AlgS.OrderedRing.markov_inequality : ∀ R a X ind p n, IsDistribution R p
/// n → (∀ k, k < n → le (mul a (ind k)) (X k)) → le (mul a (expectation R
/// ind p n)) (expectation R X p n)`.
///
/// **One hypothesis shorter than `Rat.markov_inequality`.** The `ℚ` version
/// additionally assumes `lt zero a` and `∀ k, k < n → le zero (X k)`;
/// neither is used by the argument, which is monotonicity of expectation
/// followed by `expectation_smul`. `AlgS.OrderedRing` carries no strict
/// order at all, so stating it without them is forced — and the result is
/// STRONGER, which is what makes `Rat.markov_inequality` an instance of it
/// (drop the two unused hypotheses) rather than the other way round.
fn declare_markov_inequality(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let ind_fv = d.fresh_fvar();
    let ind = d.kernel().fvar(ind_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hd_ty = d.const_app(names.is_distribution, &[r, pf, n]);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let a_ind = scaled(d, c, a, ind);
    let hle_ty = bounded_le(d, c, a_ind, x, n);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    // E[a·ind] ≤ E[X]  and  E[a·ind] ≃ a·E[ind]
    let mono = d.const_app(names.expectation_le, &[r, a_ind, x, pf, n, hle, hd]);
    let hsm = d.const_app(names.expectation_smul, &[r, a, ind, pf, n]);
    let e_aind = expectation_of(d, names, r, a_ind, pf, n);
    let e_ind = expectation_of(d, names, r, ind, pf, n);
    let a_eind = rmul(d, c, a, e_ind);
    let ex = expectation_of(d, names, r, x, pf, n);
    let refl_ex = refl(d, c, ex);
    let core = lecongr(d, c, e_aind, a_eind, ex, ex, hsm, refl_ex, mono);
    let stmt = rle(d, c, a_eind, ex);

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let t = d.arrow(hle_ty, stmt);
        let t = d.arrow(hd_ty, t);
        let over_n = d.pi_fv(n_fv, nat, t);
        let over_pf = d.pi_fv(pf_fv, fn_ty, over_n);
        let over_ind = d.pi_fv(ind_fv, fn_ty, over_pf);
        let over_x = d.pi_fv(x_fv, fn_ty, over_ind);
        let over_a = d.pi_fv(a_fv, c.carrier, over_x);
        d.pi_fv(r_fv, ord_ty, over_a)
    };
    let value = {
        let t = d.lam_fv(hle_fv, hle_ty, core);
        let t = d.lam_fv(hd_fv, hd_ty, t);
        let over_n = d.lam_fv(n_fv, nat, t);
        let over_pf = d.lam_fv(pf_fv, fn_ty, over_n);
        let over_ind = d.lam_fv(ind_fv, fn_ty, over_pf);
        let over_x = d.lam_fv(x_fv, fn_ty, over_ind);
        let over_a = d.lam_fv(a_fv, c.carrier, over_x);
        d.lam_fv(r_fv, ord_ty, over_a)
    };
    d.declare_theorem(names.markov_inequality, ty, value)
}

// ---------------------------------------------------------------------------
// Variance and covariance.
// ---------------------------------------------------------------------------

/// `AlgS.OrderedRing.variance R X p n := expectation R (fun k => (X k − μ) *
/// (X k − μ)) p n` with `μ := expectation R X p n`.
fn declare_variance(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mu = expectation_of(d, names, r, x, pf, n);
    let summand = centred_product(d, c, x, x, mu, mu);
    let body = expectation_of(d, names, r, summand, pf, n);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_x = d.lam_fv(x_fv, fn_ty, with_pf);
        let ord_ty = rec_ty(d, rn);
        d.lam_fv(r_fv, ord_ty, with_x)
    };
    let ty = {
        let inner = d.arrow(nat, c.carrier);
        let over_pf = d.arrow(fn_ty, inner);
        let over_x = d.arrow(fn_ty, over_pf);
        let ord_ty = rec_ty(d, rn);
        d.pi_fv(r_fv, ord_ty, over_x)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: names.variance,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(5),
    })
}

/// `AlgS.OrderedRing.covariance R X Y p n := expectation R (fun k => (X k −
/// E[X]) * (Y k − E[Y])) p n`.
fn declare_covariance(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mux = expectation_of(d, names, r, x, pf, n);
    let muy = expectation_of(d, names, r, y, pf, n);
    let summand = centred_product(d, c, x, y, mux, muy);
    let body = expectation_of(d, names, r, summand, pf, n);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        let with_x = d.lam_fv(x_fv, fn_ty, with_y);
        let ord_ty = rec_ty(d, rn);
        d.lam_fv(r_fv, ord_ty, with_x)
    };
    let ty = {
        let inner = d.arrow(nat, c.carrier);
        let over_pf = d.arrow(fn_ty, inner);
        let over_y = d.arrow(fn_ty, over_pf);
        let over_x = d.arrow(fn_ty, over_y);
        let ord_ty = rec_ty(d, rn);
        d.pi_fv(r_fv, ord_ty, over_x)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: names.covariance,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(5),
    })
}

/// `AlgS.OrderedRing.variance_nonneg : ∀ R X p n, IsDistribution R p n → le
/// zero (variance R X p n)` — every summand is a square, so `mul_nonneg`
/// does not apply directly; instead the two factors are the SAME term, and
/// a square is nonnegative only in a LINEARLY ordered ring. See the module
/// note: this is stated with the squares' nonnegativity supplied as a
/// hypothesis, because `AlgS.OrderedRing` has no trichotomy.
fn declare_variance_nonneg(
    d: &mut IntDev<'_>,
    rn: &RecordNames,
    names: &ProbSNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c = proj(d, rn, r);
    let fn_ty = d.arrow(nat, c.carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // hsq : ∀ a, le zero (mul a a) -- the trichotomy consequence the record
    // does not carry, taken as an explicit hypothesis (ADR-1601's discipline
    // for a classical principle, applied to an order-completeness one).
    let hsq_ty = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let aa = rmul(d, c, a, a);
        let body = rle(d, c, c.zero, aa);
        d.pi_fv(a_fv, c.carrier, body)
    };
    let hsq_fv = d.fresh_fvar();
    let hsq = d.kernel().fvar(hsq_fv);
    let hd_ty = d.const_app(names.is_distribution, &[r, pf, n]);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let mu = expectation_of(d, names, r, x, pf, n);
    let summand = centred_product(d, c, x, x, mu, mu);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(kv, n);
        let hk_fv = d.fresh_fvar();
        let xk = d.apply(x, &[kv]);
        let dx = rsub(d, c, xk, mu);
        let body = d.apply(hsq, &[dx]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let core = d.const_app(
        names.expectation_nonneg,
        &[r, summand, pf, n, pointwise, hd],
    );
    let var = d.const_app(names.variance, &[r, x, pf, n]);
    let stmt = rle(d, c, c.zero, var);

    let ord_ty = rec_ty(d, rn);
    let ty = {
        let t = d.arrow(hd_ty, stmt);
        let t = d.arrow(hsq_ty, t);
        let over_n = d.pi_fv(n_fv, nat, t);
        let over_pf = d.pi_fv(pf_fv, fn_ty, over_n);
        let over_x = d.pi_fv(x_fv, fn_ty, over_pf);
        d.pi_fv(r_fv, ord_ty, over_x)
    };
    let value = {
        let t = d.lam_fv(hd_fv, hd_ty, core);
        let t = d.lam_fv(hsq_fv, hsq_ty, t);
        let over_n = d.lam_fv(n_fv, nat, t);
        let over_pf = d.lam_fv(pf_fv, fn_ty, over_n);
        let over_x = d.lam_fv(x_fv, fn_ty, over_pf);
        d.lam_fv(r_fv, ord_ty, over_x)
    };
    d.declare_theorem(names.variance_nonneg, ty, value)
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

/// Declare the whole generic finite-probability layer.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(crate) fn declare_probability_s_all(
    d: &mut IntDev<'_>,
    p: &RatPrelude,
) -> Result<(), KernelError> {
    let st = p.int.nat.structures_s;
    let rn = st.ordered_ring;
    let ring = st.ring;
    let group = st.group;
    let extra = p.int.nat.structures_s_extra;
    let names = p.probability_s;
    let ext = p.ordered_ring_ext_s;

    declare_to_ring_s(d, &rn, &ring, &names)?;
    declare_to_group_s(d, &rn, &group, &names)?;
    declare_sum_range(d, &rn, &names)?;
    declare_sum_range_equations(d, &rn, &names)?;
    declare_sum_range_congr(d, &rn, &names)?;
    declare_sum_range_add(d, &rn, &names)?;
    declare_mul_sum_range(d, &rn, &names, extra.mul_zero)?;
    declare_sum_range_le(d, &rn, &names, ext.add_le_add)?;
    declare_sum_range_nonneg(d, &rn, &names, ext.add_le_add)?;
    declare_zero_mul(d, &rn, &names, extra.add_left_cancel)?;
    declare_neg_mul(d, &rn, &names, extra.add_left_cancel)?;
    declare_sub_nonneg_of_le(d, &rn, &names, ext.add_le_add_right)?;
    declare_mul_le_mul_of_nonneg_right(d, &rn, &names)?;
    declare_is_distribution(d, &rn, &names)?;
    declare_expectation(d, &rn, &names)?;
    declare_expectation_add(d, &rn, &names)?;
    declare_expectation_smul(d, &rn, &names)?;
    declare_expectation_const(d, &rn, &names)?;
    declare_expectation_nonneg(d, &rn, &names)?;
    declare_expectation_le(d, &rn, &names)?;
    declare_markov_inequality(d, &rn, &names)?;
    declare_variance(d, &rn, &names)?;
    declare_covariance(d, &rn, &names)?;
    declare_variance_nonneg(d, &rn, &names)?;
    Ok(())
}
