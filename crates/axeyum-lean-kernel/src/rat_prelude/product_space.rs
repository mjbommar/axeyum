//! ADR-1677: **the k-fold product probability space at ℚ**, built on the
//! function-space aggregate `Rat.sumMaps` that ADR-1543 already declared.
//!
//! ## Why this file exists where it does
//!
//! `probability.rs` and `probability_s.rs` are one weight function over one
//! index range. `Independent A B p n := E[A·B] = E[A]·E[B]` is a
//! **definition** there: the two-fold product rule is assumed at the point of
//! use, because there is no second space to take a product with.
//! `fourth_moment.rs`'s own header records the consequence — "independence is
//! not expressible here (there is no product space)" — and settles for
//! four-wise uncorrelatedness instead.
//!
//! The lane brief that produced this file measured the shelf by NAME and
//! concluded no product structure existed. Measured by STEP, it does. The step
//! a product space needs is *a finite sum indexed by tuples*, and that is
//! exactly [`RatPrelude::sum_maps`](super::RatPrelude::sum_maps):
//!
//! ```text
//! sumMaps 0       n F  = F (fun _ => 0)
//! sumMaps (m + 1) n F  = sumRange (fun k => sumMaps m n (fun g => F (cons k g))) n
//! ```
//!
//! `sumMaps m n` ranges over every map `[0,m) → [0,n)` — the product of `m`
//! copies of the index range `[0,n)`. It was built for Cauchy–Binet, where the
//! maps are row selections; here they are the points of a product space and
//! nothing about the construction changes.
//!
//! ## The one theorem that was missing, and what it is
//!
//! `Int.prodRange_sumRange_expand` (the generalized distributive law) says
//!
//! ```text
//! ∏_{i<m} ( ∑_{k<n} c i k )  =  ∑_g ∏_{i<m} c i (g i)
//! ```
//!
//! and that is the product-weight normalisation identity with the weights left
//! uninstantiated. `Rat` had every ingredient the `Int` proof consumes
//! (`prodRange_shiftFront`, `sumMaps_congr`, `sumMaps_mul_left`,
//! `sumRange_congr`, `sumRange_mul_right`) and not the theorem itself.
//! [`declare_prod_range_sum_range_expand`] is the port, and it does two jobs
//! at once:
//!
//! * at `c i := P i` it gives [`declare_prod_weight_sum_maps_one`] — the
//!   product weight is again a distribution;
//! * at `c i k := f i k * P i k` it gives, after one
//!   [`declare_prod_range_mul`], the **k-fold product rule for expectations**
//!   `E[∏_{i<m} f_i] = ∏_{i<m} E_{P_i}[f_i]` — [`declare_k_independent_prod_weight`].
//!
//! ## Why ℚ and not `AlgS.OrderedRing`
//!
//! ADR-1677's sizing: the generic layer has neither `sumMaps` (porting it into
//! setoid form is ≥ 1,256 lines, the current size of `rat_prelude/sum_maps.rs`,
//! and strictly larger because every `Eq` rewrite becomes an explicit
//! congruence step) nor `mulComm`, which ADR-1592 §2 deliberately left off
//! `AlgS.OrderedRing` — and the four-factor regrouping
//! `(F·G)·(f·g) = (F·f)·(G·g)` inside [`declare_prod_range_mul`] is exactly a
//! commutativity step. At ℚ it is one `ring::rat` identity.
//!
//! ## `KIndependent` is a predicate WITH a witness
//!
//! [`declare_k_independent`] states k-fold independence as the shelf's
//! interface — the form a downstream theorem quantifies over. Standing alone
//! it would be a hypothesis nothing can discharge, i.e. an axiom in disguise.
//! [`declare_k_independent_prod_weight`] is what stops that: the constructed
//! product weight satisfies it. [`declare_sum_maps_one_of_k_independent`] is
//! then a consequence proved from the PREDICATE (not from the construction):
//! k-fold independence with normalised marginals forces the joint weight to be
//! normalised too.
//!
//! Every definition here is checked by **evaluation** at small concrete
//! arguments, not by the trusted gate — `(Nat → Nat → Rat) → Nat → (Nat → Nat)
//! → Rat` is that type whatever the function returns. See
//! `product_space_tests.rs`.

use super::RatPrelude;
use super::ops::{
    rat_ty, rchain, rcongr, req, rle, rmul, rone, rrefl, rsum_range, rsymm, rtrans, rzero,
};
use super::sum_maps::{cons_fn, fam_ty, map_ty, rprod_range, rsum_maps};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.prodWeight`: above `Rat.prodRange` (35) and
/// `Rat.sumMaps` (36), following the "outranks everything it unfolds to"
/// convention `rat_prelude/sum_maps.rs` set.
const PROD_WEIGHT_HEIGHT: u16 = 37;

/// Delta height for `Rat.expectationMaps`, which unfolds to `Rat.sumMaps`.
const EXPECTATION_MAPS_HEIGHT: u16 = 38;

/// Delta height for `Rat.KIndependent`, which unfolds to
/// `Rat.expectationMaps` and `Rat.prodRange`.
const K_INDEPENDENT_HEIGHT: u16 = 39;

/// The names this module declares, all under the `Rat` root.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProductSpaceNames {
    /// `Rat.prodRange_one : ∀ n, prodRange (fun _ => one) n = one`.
    pub prod_range_one: NameId,
    /// `Rat.prodRange_mul : ∀ f g n,
    /// prodRange (fun i => f i * g i) n = prodRange f n * prodRange g n`.
    pub prod_range_mul: NameId,
    /// `Rat.prodRange_sumRange_expand : ∀ n m c,
    /// prodRange (fun i => sumRange (c i) n) m
    ///   = sumMaps m n (fun g => prodRange (fun i => c i (g i)) m)` — the ℚ
    /// port of `Int.prodRange_sumRange_expand`, and the engine of everything
    /// below.
    pub prod_range_sum_range_expand: NameId,
    /// `Rat.prodWeight : (Nat → Nat → Rat) → Nat → (Nat → Nat) → Rat`,
    /// `prodWeight P m g := prodRange (fun i => P i (g i)) m` — the product
    /// weight of `m` marginals at the product-space point `g`.
    pub prod_weight: NameId,
    /// `Rat.prodWeight_nonneg : ∀ P, (∀ i j, le zero (P i j)) → ∀ g m,
    /// le zero (prodWeight P m g)`.
    pub prod_weight_nonneg: NameId,
    /// `Rat.prodWeight_sumMaps_one : ∀ n P m, (∀ i, sumRange (P i) n = one) →
    /// sumMaps m n (prodWeight P m) = one` — **the product weight is again a
    /// distribution**.
    pub prod_weight_sum_maps_one: NameId,
    /// `Rat.expectationMaps : Nat → Nat → ((Nat → Nat) → Rat) →
    /// ((Nat → Nat) → Rat) → Rat`,
    /// `expectationMaps m n F W := sumMaps m n (fun g => F g * W g)` — the
    /// same normalized weighted sum `Rat.expectation` is, over the product
    /// index set instead of a range.
    pub expectation_maps: NameId,
    /// `Rat.KIndependent m n P W := ∀ f, expectationMaps m n
    /// (fun g => prodRange (fun i => f i (g i)) m) W
    ///   = prodRange (fun i => expectation (f i) (P i) n) m` — **the k-fold
    /// independence statement**: the `m` coordinates of `W` factor, with
    /// marginals `P`.
    pub k_independent: NameId,
    /// `Rat.kIndependent_prodWeight : ∀ n m P, KIndependent m n P
    /// (prodWeight P m)` — the witness, and equivalently the **k-fold product
    /// rule for expectations**.
    pub k_independent_prod_weight: NameId,
    /// `Rat.sumMaps_one_of_kIndependent : ∀ n m P W, KIndependent m n P W →
    /// (∀ i, sumRange (P i) n = one) → sumMaps m n W = one` — a consequence
    /// proved from the PREDICATE: independence with normalised marginals
    /// forces the joint to be normalised.
    pub sum_maps_one_of_k_independent: NameId,
}

/// Intern the names under the `Rat` root.
pub(crate) fn intern_product_space(k: &mut Kernel) -> ProductSpaceNames {
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    ProductSpaceNames {
        prod_range_one: k.name_str(rat, "prodRange_one"),
        prod_range_mul: k.name_str(rat, "prodRange_mul"),
        prod_range_sum_range_expand: k.name_str(rat, "prodRange_sumRange_expand"),
        prod_weight: k.name_str(rat, "prodWeight"),
        prod_weight_nonneg: k.name_str(rat, "prodWeight_nonneg"),
        prod_weight_sum_maps_one: k.name_str(rat, "prodWeight_sumMaps_one"),
        expectation_maps: k.name_str(rat, "expectationMaps"),
        k_independent: k.name_str(rat, "KIndependent"),
        k_independent_prod_weight: k.name_str(rat, "kIndependent_prodWeight"),
        sum_maps_one_of_k_independent: k.name_str(rat, "sumMaps_one_of_kIndependent"),
    }
}

/// Declare the whole product-probability layer.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(crate) fn declare_product_space_all(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    declare_prod_range_one(d, p)?;
    declare_prod_range_mul(d, p)?;
    declare_prod_range_sum_range_expand(d, p)?;
    declare_prod_weight(d, p)?;
    declare_prod_weight_nonneg(d, p)?;
    declare_prod_weight_sum_maps_one(d, p)?;
    declare_expectation_maps(d, p)?;
    declare_k_independent(d, p)?;
    declare_k_independent_prod_weight(d, p)?;
    declare_sum_maps_one_of_k_independent(d, p)?;
    Ok(())
}

// --- shared shapes ---------------------------------------------------------

/// `Nat → Rat`, a range-indexed family.
fn seq_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    d.arrow(nat, carrier)
}

/// `Nat → Nat → Rat`, a FAMILY of range-indexed families — one marginal (or
/// one random variable) per factor.
fn coef_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let inner = seq_ty(d);
    d.arrow(nat, inner)
}

/// `fun _ : Nat => Rat.one` — the constant-one sequence every normalisation
/// step collapses to.
fn const_one(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    let nat = d.nat_ty();
    let one_r = rone(d, p);
    let i_fv = d.fresh_fvar();
    d.lam_fv(i_fv, nat, one_r)
}

/// `fun i => c i (g i)` — the coefficient family `c` read along the
/// product-space point `g`.
fn along(d: &mut IntDev<'_>, c: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let gi = d.apply(g, &[i]);
    let body = d.apply(c, &[i, gi]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun g => prodRange (fun i => c i (g i)) x` — the product-weight shape,
/// spelled as a literal lambda where a proof needs it (the same reason
/// `probability::weighted` exists).
fn picks(d: &mut IntDev<'_>, p: RatPrelude, c: ExprId, x: ExprId) -> ExprId {
    let map_t = map_ty(d);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let inner = along(d, c, g);
    let body = rprod_range(d, p, inner, x);
    d.lam_fv(g_fv, map_t, body)
}

/// `fun i => sumRange (c i) n`, the row of sums the expansion starts from.
fn rows(d: &mut IntDev<'_>, p: RatPrelude, c: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ci = d.apply(c, &[i]);
    let body = rsum_range(d, p, ci, n);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => c (succ i)`.
fn tail(d: &mut IntDev<'_>, c: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let si = d.succ(i);
    let body = d.apply(c, &[si]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => f i * g i`, the pointwise product of two sequences.
fn pointwise_mul(d: &mut IntDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let body = rmul(d, fi, gi);
    d.lam_fv(i_fv, nat, body)
}

/// `Rat.prodWeight` applied at `pp`, `m`.
fn rprod_weight(d: &mut IntDev<'_>, p: RatPrelude, pp: ExprId, m: ExprId) -> ExprId {
    d.const_app(p.product_space.prod_weight, &[pp, m])
}

/// `Rat.expectationMaps` applied at `m`, `n`, `f`, `w`.
fn rexpectation_maps(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    n: ExprId,
    f: ExprId,
    w: ExprId,
) -> ExprId {
    d.const_app(p.product_space.expectation_maps, &[m, n, f, w])
}

/// `Eq Rat (mul one a) a`, derived from `mul_comm` and `mul_one`.
///
/// This prelude declares `Rat.mul_one` and not `Rat.one_mul`; the same
/// derivation `rat_prelude/sum_maps.rs` does inline, repeated here rather than
/// widening that module's surface for one caller.
fn one_mul(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId) -> ExprId {
    let one_r = rone(d, p);
    let lhs = rmul(d, one_r, a);
    let mid = rmul(d, a, one_r);
    let comm = d.lemma(p.mul_comm, &[one_r, a]);
    let mo = d.lemma(p.mul_one, &[a]);
    rtrans(d, lhs, mid, a, comm, mo)
}

/// A commutative-ring rearrangement at ℚ, emitted by [`crate::ring::rat`]
/// (ADR-1582). Every use below is a regrouping of four opaque atoms whose two
/// sides have identical normal forms, so a decline is a bug in the caller's
/// shapes, not a mathematical gap.
fn rring(d: &mut IntDev<'_>, p: RatPrelude, lhs: ExprId, rhs: ExprId) -> ExprId {
    crate::ring::rat::prove_eq(d, &p, lhs, rhs)
        .expect("product_space: a commutative-ring rearrangement must be a ring identity")
}

// --- Rat.prodRange_one -----------------------------------------------------

/// `Rat.prodRange_one : ∀ n, prodRange (fun _ => one) n = one`.
///
/// Induction on `n`; the base case is `Eq.refl` because `prodRange f 0`
/// ι-reduces to `Rat.one`, and the step is one `Rat.mul_one`.
fn declare_prod_range_one(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let ones = const_one(d, p);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = rprod_range(d, p, ones, x);
        let one_r = rone(d, p);
        req(d, lhs, one_r)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let one_r = rone(d, p);
            rrefl(d, one_r)
        },
        &|d, j, ih| {
            let one_r = rone(d, p);
            let prior = rprod_range(d, p, ones, j);
            let start = rmul(d, prior, one_r);
            let h1 = d.lemma(p.mul_one, &[prior]);
            let (_, chained) = rchain(d, start, &[(prior, h1), (one_r, ih)]);
            chained
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.product_space.prod_range_one, ty, value)
}

// --- Rat.prodRange_mul -----------------------------------------------------

/// `Rat.prodRange_mul : ∀ f g n,
/// prodRange (fun i => f i * g i) n = prodRange f n * prodRange g n`.
///
/// Induction on `n`. The base case is `one = one * one`, i.e. `mul_one`
/// reversed; the step is the four-factor regrouping
/// `(F·G)·(f·g) = (F·f)·(G·g)`, which is where **commutativity is spent** —
/// the reason ADR-1677 puts this file at ℚ and not over `AlgS.OrderedRing`.
fn declare_prod_range_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let fn_ty = seq_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let ptw = pointwise_mul(d, f, g);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = rprod_range(d, p, ptw, x);
        let pf = rprod_range(d, p, f, x);
        let pg = rprod_range(d, p, g, x);
        let rhs = rmul(d, pf, pg);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let one_r = rone(d, p);
            let sq = rmul(d, one_r, one_r);
            let fwd = d.lemma(p.mul_one, &[one_r]);
            rsymm(d, sq, one_r, fwd)
        },
        &|d, j, ih| {
            let a = rprod_range(d, p, ptw, j);
            let pf = rprod_range(d, p, f, j);
            let pg = rprod_range(d, p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let step = rmul(d, fj, gj);

            let start = rmul(d, a, step);
            let joined = rmul(d, pf, pg);
            let mid = rmul(d, joined, step);
            let h1 = rcongr(d, a, joined, ih, &|d, t| rmul(d, t, step));

            let left = rmul(d, pf, fj);
            let right = rmul(d, pg, gj);
            let target = rmul(d, left, right);
            let h2 = rring(d, p, mid, target);

            let (_, chained) = rchain(d, start, &[(mid, h1), (target, h2)]);
            chained
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.product_space.prod_range_mul, ty, value)
}

// --- Rat.prodRange_sumRange_expand -----------------------------------------

/// `Rat.prodRange_sumRange_expand : ∀ n m c,
/// prodRange (fun i => sumRange (c i) n) m
///   = sumMaps m n (fun g => prodRange (fun i => c i (g i)) m)`.
///
/// **The generalized distributive law** — a product of `m` sums of `n` terms
/// each expands into a sum over all `n^m` maps `[0,m) → [0,n)`. The ℚ port of
/// `Int.prodRange_sumRange_expand`, shape for shape.
///
/// Induction on `m`, motive quantified over `c` because the successor step
/// applies the induction hypothesis at `fun i => c (succ i)`. Both ends of the
/// step peel their FIRST factor with `Rat.prodRange_shiftFront`, which is what
/// makes `cons`'s two `Eq.refl` equations line up with no side conditions.
fn declare_prod_range_sum_range_expand(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let map_t = map_ty(d);
    let cty = coef_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let r = rows(d, p, c, n);
        let lhs = rprod_range(d, p, r, x);
        let pk = picks(d, p, c, x);
        let rhs = rsum_maps(d, p, x, n, pk);
        let eq = req(d, lhs, rhs);
        d.pi_fv(c_fv, cty, eq)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            // Both sides reduce to Rat.one: prodRange _ 0 ≡ one, and
            // sumMaps 0 n (picks c 0) ≡ picks c 0 junk ≡ prodRange _ 0 ≡ one.
            let c_fv = d.fresh_fvar();
            let one_r = rone(d, p);
            let refl = rrefl(d, one_r);
            d.lam_fv(c_fv, cty, refl)
        },
        &|d, j, ih| {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let sj = d.succ(j);

            let r = rows(d, p, c, n);
            let start = rprod_range(d, p, r, sj);

            let zero_n = d.zero();
            let c0 = d.apply(c, &[zero_n]);
            let head_sum = rsum_range(d, p, c0, n);
            let tc = tail(d, c);
            let tail_rows = rows(d, p, tc, n);
            let tail_prod = rprod_range(d, p, tail_rows, j);
            let t1 = rmul(d, head_sum, tail_prod);
            let h1 = d.lemma(p.prod_range_shift_front, &[r, j]);

            let tail_picks = picks(d, p, tc, j);
            let tail_maps = rsum_maps(d, p, j, n, tail_picks);
            let t2 = rmul(d, head_sum, tail_maps);
            let ih_at_tail = d.apply(ih, &[tc]);
            let h2 = rcongr(d, tail_prod, tail_maps, ih_at_tail, &|d, t| {
                rmul(d, head_sum, t)
            });

            // The other end: RHS ≡ sumRange (fun k => sumMaps j n (fun g =>
            //   picks c (succ j) (cons k g))) n, and each inner body peels to
            //   mul (c 0 k) (picks (tail c) j g) by prodRange_shiftFront,
            //   because cons k g 0 ≡ k and cons k g (succ i) ≡ g i.
            let shifted_body = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let cg = cons_fn(d, k, g);
                let pk = picks(d, p, c, sj);
                let body = d.apply(pk, &[cg]);
                d.lam_fv(g_fv, map_t, body)
            };
            let scaled_body = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let ck = d.apply(c, &[zero_n, k]);
                let tp = picks(d, p, tc, j);
                let tpg = d.apply(tp, &[g]);
                let body = rmul(d, ck, tpg);
                d.lam_fv(g_fv, map_t, body)
            };

            let rhs_summand = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sb = shifted_body(d, k);
                let body = rsum_maps(d, p, j, n, sb);
                d.lam_fv(k_fv, nat, body)
            };
            let mid_summand = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sb = scaled_body(d, k);
                let body = rsum_maps(d, p, j, n, sb);
                d.lam_fv(k_fv, nat, body)
            };
            let pulled_summand = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let ck = d.apply(c, &[zero_n, k]);
                let body = rmul(d, ck, tail_maps);
                d.lam_fv(k_fv, nat, body)
            };

            let per_k_congr = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sb = shifted_body(d, k);
                let cb = scaled_body(d, k);
                let pointwise = {
                    let g_fv = d.fresh_fvar();
                    let g = d.kernel().fvar(g_fv);
                    let cg = cons_fn(d, k, g);
                    let inner = along(d, c, cg);
                    let sf = d.lemma(p.prod_range_shift_front, &[inner, j]);
                    d.lam_fv(g_fv, map_t, sf)
                };
                let body = d.lemma(p.sum_maps_congr, &[n, j, sb, cb, pointwise]);
                d.lam_fv(k_fv, nat, body)
            };
            let per_k_pull = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let ck = d.apply(c, &[zero_n, k]);
                let tp = picks(d, p, tc, j);
                let body = d.lemma(p.sum_maps_mul_left, &[n, ck, j, tp]);
                d.lam_fv(k_fv, nat, body)
            };

            let rhs_full = rsum_range(d, p, rhs_summand, n);
            let mid_full = rsum_range(d, p, mid_summand, n);
            let pulled_full = rsum_range(d, p, pulled_summand, n);
            let s1 = d.lemma(
                p.sum_range_congr,
                &[rhs_summand, mid_summand, n, per_k_congr],
            );
            let s2 = d.lemma(
                p.sum_range_congr,
                &[mid_summand, pulled_summand, n, per_k_pull],
            );
            let s3 = d.lemma(p.sum_range_mul_right, &[c0, tail_maps, n]);
            let (_, rhs_to_t2) =
                rchain(d, rhs_full, &[(mid_full, s1), (pulled_full, s2), (t2, s3)]);
            let h3 = rsymm(d, rhs_full, t2, rhs_to_t2);

            let (_, chained) = rchain(d, start, &[(t1, h1), (t2, h2), (rhs_full, h3)]);
            d.lam_fv(c_fv, cty, chained)
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        d.pi_fv(n_fv, nat, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        d.lam_fv(n_fv, nat, over_m)
    };
    d.declare_theorem(p.product_space.prod_range_sum_range_expand, ty, value)
}

// --- Rat.prodWeight --------------------------------------------------------

/// Admit `Rat.prodWeight : (Nat → Nat → Rat) → Nat → (Nat → Nat) → Rat`,
/// `prodWeight P m g := prodRange (fun i => P i (g i)) m`.
///
/// The `m` marginals are `P 0 … P (m-1)`, each a weight on the index range;
/// `g` is a point of the product space, i.e. a choice of one index per factor.
/// The bound `m` comes BEFORE the point so that `prodWeight P m` is itself a
/// `(Nat → Nat) → Rat` and can be handed to `Rat.sumMaps m n` directly.
fn declare_prod_weight(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let map_t = map_ty(d);
    let cty = coef_ty(d);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    let inner = along(d, pp, g);
    let body = rprod_range(d, p, inner, m);

    let value = {
        let with_g = d.lam_fv(g_fv, map_t, body);
        let with_m = d.lam_fv(m_fv, nat, with_g);
        d.lam_fv(pp_fv, cty, with_m)
    };
    let ty = {
        let over_g = d.arrow(map_t, carrier);
        let over_m = d.arrow(nat, over_g);
        d.arrow(cty, over_m)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.product_space.prod_weight,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PROD_WEIGHT_HEIGHT),
    })
}

/// `Rat.prodWeight_nonneg : ∀ P, (∀ i j, le zero (P i j)) → ∀ g m,
/// le zero (prodWeight P m g)`.
///
/// Induction on `m`: the base case is `Rat.zero_lt_one` weakened by
/// `Rat.le_of_lt`, the step one `Rat.mul_nonneg`.
///
/// The hypothesis is UNBOUNDED (`∀ i j`, not `∀ i < m, ∀ j < n`) on purpose:
/// the bounded form would force every consumer to carry the point's range
/// bound `MapsInto g n` as well, and `Rat.sumMaps` does not hand one out — the
/// maps it enumerates are `cons` towers over the constant-zero map, which is
/// exactly why `Rat.sumMaps_congr_mapsInto` had to exist for the determinant
/// route. Every distribution in this development is a total nonnegative
/// function, so the unbounded form costs nothing at the point of use.
fn declare_prod_weight_nonneg(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let map_t = map_ty(d);
    let cty = coef_ty(d);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pij = d.apply(pp, &[i, j]);
        let zero_r = rzero(d, p);
        let body = rle(d, p, zero_r, pij);
        let over_j = d.pi_fv(j_fv, nat, body);
        d.pi_fv(i_fv, nat, over_j)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let w = rprod_weight(d, p, pp, x);
        let wg = d.apply(w, &[g]);
        let zero_r = rzero(d, p);
        rle(d, p, zero_r, wg)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_r = rzero(d, p);
            let one_r = rone(d, p);
            let lt = d.kernel().const_(p.zero_lt_one, vec![]);
            d.lemma(p.le_of_lt, &[zero_r, one_r, lt])
        },
        &|d, j, ih| {
            let inner = along(d, pp, g);
            let prior = rprod_range(d, p, inner, j);
            let gj = d.apply(g, &[j]);
            let step = d.apply(pp, &[j, gj]);
            let h_step = d.apply(h, &[j, gj]);
            d.lemma(p.mul_nonneg, &[prior, step, ih, h_step])
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, map_t, over_m);
        let with_h = d.pi_fv(h_fv, hyp_ty, over_g);
        d.pi_fv(pp_fv, cty, with_h)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, map_t, over_m);
        let with_h = d.lam_fv(h_fv, hyp_ty, over_g);
        d.lam_fv(pp_fv, cty, with_h)
    };
    d.declare_theorem(p.product_space.prod_weight_nonneg, ty, value)
}

/// `Rat.prodWeight_sumMaps_one : ∀ n P m, (∀ i, sumRange (P i) n = one) →
/// sumMaps m n (prodWeight P m) = one`.
///
/// **The normalisation — the product weight is again a distribution.** Read
/// [`declare_prod_range_sum_range_expand`] backwards at `c := P`: the sum over
/// the product index set is the product of the marginal sums, and every
/// marginal sums to one, so `Rat.prodRange_congr` collapses the product to
/// `prodRange (fun _ => one) m` and [`declare_prod_range_one`] finishes.
///
/// Nonnegativity is [`declare_prod_weight_nonneg`], stated separately because
/// it needs a different hypothesis; together they are `IsDistribution`'s two
/// components transported to the product index set.
fn declare_prod_weight_sum_maps_one(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let cty = coef_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let pi = d.apply(pp, &[i]);
        let s = rsum_range(d, p, pi, n);
        let one_r = rone(d, p);
        let body = req(d, s, one_r);
        d.pi_fv(i_fv, nat, body)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let r = rows(d, p, pp, n);
    let ones = const_one(d, p);
    let pk = picks(d, p, pp, m);
    let start = rsum_maps(d, p, m, n, pk);
    let prod_rows = rprod_range(d, p, r, m);
    let prod_ones = rprod_range(d, p, ones, m);
    let one_r = rone(d, p);

    let expand = d.lemma(p.product_space.prod_range_sum_range_expand, &[n, m, pp]);
    let back = rsymm(d, prod_rows, start, expand);
    let collapse = {
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let body = d.apply(h, &[i]);
            d.lam_fv(i_fv, nat, body)
        };
        d.lemma(p.prod_range_congr, &[r, ones, m, pointwise])
    };
    let finish = d.lemma(p.product_space.prod_range_one, &[m]);
    let (_, proof) = rchain(
        d,
        start,
        &[(prod_rows, back), (prod_ones, collapse), (one_r, finish)],
    );

    let stmt = {
        let w = rprod_weight(d, p, pp, m);
        let lhs = rsum_maps(d, p, m, n, w);
        req(d, lhs, one_r)
    };
    let ty = {
        let with_h = d.arrow(hyp_ty, stmt);
        let over_m = d.pi_fv(m_fv, nat, with_h);
        let over_pp = d.pi_fv(pp_fv, cty, over_m);
        d.pi_fv(n_fv, nat, over_pp)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let over_m = d.lam_fv(m_fv, nat, with_h);
        let over_pp = d.lam_fv(pp_fv, cty, over_m);
        d.lam_fv(n_fv, nat, over_pp)
    };
    d.declare_theorem(p.product_space.prod_weight_sum_maps_one, ty, value)
}

// --- Rat.expectationMaps and the k-fold independence statement -------------

/// Admit `Rat.expectationMaps : Nat → Nat → ((Nat → Nat) → Rat) →
/// ((Nat → Nat) → Rat) → Rat`,
/// `expectationMaps m n F W := sumMaps m n (fun g => F g * W g)`.
///
/// The SAME normalized weighted sum `Rat.expectation X p n` is, with the index
/// range replaced by the product index set. The argument order follows
/// `Rat.sumMaps m n F` rather than `Rat.expectation X p n` so the bounds stay
/// leftmost and the two function arguments stay adjacent.
fn declare_expectation_maps(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let map_t = map_ty(d);
    let fam = fam_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);

    let weighted = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let fg = d.apply(f, &[g]);
        let wg = d.apply(w, &[g]);
        let body = rmul(d, fg, wg);
        d.lam_fv(g_fv, map_t, body)
    };
    let body = rsum_maps(d, p, m, n, weighted);

    let value = {
        let with_w = d.lam_fv(w_fv, fam, body);
        let with_f = d.lam_fv(f_fv, fam, with_w);
        let with_n = d.lam_fv(n_fv, nat, with_f);
        d.lam_fv(m_fv, nat, with_n)
    };
    let ty = {
        let over_w = d.arrow(fam, carrier);
        let over_f = d.arrow(fam, over_w);
        let over_n = d.arrow(nat, over_f);
        d.arrow(nat, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.product_space.expectation_maps,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXPECTATION_MAPS_HEIGHT),
    })
}

/// `fun g => prodRange (fun i => f i (g i)) m` — the product random variable
/// whose expectation the k-fold rule factors.
fn prod_var(d: &mut IntDev<'_>, p: RatPrelude, f: ExprId, m: ExprId) -> ExprId {
    picks(d, p, f, m)
}

/// `fun i => expectation (f i) (P i) n` — the marginal expectations the k-fold
/// rule factors INTO.
fn marginal_expectations(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    f: ExprId,
    pp: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let pi = d.apply(pp, &[i]);
    let body = d.const_app(p.expectation, &[fi, pi, n]);
    d.lam_fv(i_fv, nat, body)
}

/// Admit `Rat.KIndependent : Nat → Nat → (Nat → Nat → Rat) →
/// ((Nat → Nat) → Rat) → Prop`,
///
/// ```text
/// KIndependent m n P W :=
///   ∀ f, expectationMaps m n (fun g => prodRange (fun i => f i (g i)) m) W
///        = prodRange (fun i => expectation (f i) (P i) n) m
/// ```
///
/// **The k-fold independence statement the shelf needs.** `W` is a weight on
/// the product index set; `P i` is the intended law of the `i`-th coordinate.
/// The predicate says every product of coordinate functions factors — for `f
/// i` an indicator this is `Pr(⋂ A_i) = ∏ Pr(A_i)`, and for general `f i` it
/// is the product rule for expectations.
///
/// It is quantified over ALL families `f` rather than stated for indicators
/// only, for the same reason `Rat.Independent` is: the two readings then share
/// one declaration, and the witness below proves the stronger one anyway.
///
/// A predicate nothing can discharge is an axiom in disguise;
/// [`declare_k_independent_prod_weight`] is why this one is not.
fn declare_k_independent(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let anon = d.anon_name();
    let fam = fam_ty(d);
    let cty = coef_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);

    let body = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let var = prod_var(d, p, f, m);
        let lhs = rexpectation_maps(d, p, m, n, var, w);
        let marg = marginal_expectations(d, p, f, pp, n);
        let rhs = rprod_range(d, p, marg, m);
        let eq = req(d, lhs, rhs);
        d.pi_fv(f_fv, cty, eq)
    };

    let value = {
        let with_w = d.lam_fv(w_fv, fam, body);
        let with_pp = d.lam_fv(pp_fv, cty, with_w);
        let with_n = d.lam_fv(n_fv, nat, with_pp);
        d.lam_fv(m_fv, nat, with_n)
    };
    let ty = {
        let over_w = d.arrow(fam, prop);
        let over_pp = d.arrow(cty, over_w);
        let over_n = d
            .kernel()
            .pi(anon, nat, over_pp, crate::BinderInfo::Default);
        d.kernel().pi(anon, nat, over_n, crate::BinderInfo::Default)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.product_space.k_independent,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(K_INDEPENDENT_HEIGHT),
    })
}

/// `Rat.kIndependent_prodWeight : ∀ n m P, KIndependent m n P (prodWeight P m)`.
///
/// **The witness, and the k-fold product rule for expectations.** Unfolded it
/// says
///
/// ```text
/// ∑_g ( ∏_{i<m} f i (g i) ) · ( ∏_{i<m} P i (g i) )  =  ∏_{i<m} E_{P i}[f i]
/// ```
///
/// Two steps, no induction of its own:
///
/// 1. [`declare_prod_range_sum_range_expand`] at `c i k := f i k * P i k`
///    turns the right side — which is `∏_i ∑_k f i k · P i k` once
///    `Rat.expectation` is unfolded — into `∑_g ∏_i (f i (g i) · P i (g i))`;
/// 2. `Rat.sumMaps_congr` with [`declare_prod_range_mul`] at each point `g`
///    splits that single product into the two the left side has.
///
/// Nothing here is specific to weights: it holds for arbitrary `f` and `P`.
/// The probabilistic reading is what the hypothesis-free statement BUYS —
/// `prodWeight P m` being a distribution is [`declare_prod_weight_sum_maps_one`]
/// and is not needed to factor an expectation.
fn declare_k_independent_prod_weight(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let map_t = map_ty(d);
    let cty = coef_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    // c i k := f i k * P i k -- the coefficient family whose expansion IS the
    // right-hand side, because `Rat.expectation (f i) (P i) n` is by
    // definition `sumRange (fun k => f i k * P i k) n`.
    let c = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fik = d.apply(f, &[i, k]);
        let pik = d.apply(pp, &[i, k]);
        let body = rmul(d, fik, pik);
        let over_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(i_fv, nat, over_k)
    };

    let r = rows(d, p, c, n);
    let t2 = rprod_range(d, p, r, m);
    let joint = picks(d, p, c, m);
    let t1 = rsum_maps(d, p, m, n, joint);
    let split = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let fg = along(d, f, g);
        let pg = along(d, pp, g);
        let left = rprod_range(d, p, fg, m);
        let right = rprod_range(d, p, pg, m);
        let body = rmul(d, left, right);
        d.lam_fv(g_fv, map_t, body)
    };
    let t0 = rsum_maps(d, p, m, n, split);

    let h_b = d.lemma(p.product_space.prod_range_sum_range_expand, &[n, m, c]);
    let h_a = {
        let pointwise = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let fg = along(d, f, g);
            let pg = along(d, pp, g);
            let body = d.lemma(p.product_space.prod_range_mul, &[fg, pg, m]);
            d.lam_fv(g_fv, map_t, body)
        };
        d.lemma(p.sum_maps_congr, &[n, m, joint, split, pointwise])
    };
    let t2_to_t0 = rtrans(d, t2, t1, t0, h_b, h_a);
    let proof = rsymm(d, t2, t0, t2_to_t0);

    let stmt = {
        let w = rprod_weight(d, p, pp, m);
        d.const_app(p.product_space.k_independent, &[m, n, pp, w])
    };
    let ty = {
        let over_pp = d.pi_fv(pp_fv, cty, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_pp);
        d.pi_fv(n_fv, nat, over_m)
    };
    let value = {
        let over_f = d.lam_fv(f_fv, cty, proof);
        let over_pp = d.lam_fv(pp_fv, cty, over_f);
        let over_m = d.lam_fv(m_fv, nat, over_pp);
        d.lam_fv(n_fv, nat, over_m)
    };
    d.declare_theorem(p.product_space.k_independent_prod_weight, ty, value)
}

/// `Rat.sumMaps_one_of_kIndependent : ∀ n m P W, KIndependent m n P W →
/// (∀ i, sumRange (P i) n = one) → sumMaps m n W = one`.
///
/// **A consequence proved from the PREDICATE, not from the construction.**
/// Instantiate independence at the constant-one family `f i k := one`. On the
/// left the product random variable collapses to `1` at every point, so the
/// expectation is the total mass `∑_g W g`; on the right every marginal
/// expectation is `∑_k 1 · P i k = ∑_k P i k = 1`, so the product is `1`.
///
/// The point is that it holds for ANY `W` satisfying the predicate — it is not
/// a re-proof of [`declare_prod_weight_sum_maps_one`] through the witness. It
/// says k-fold independence with normalised marginals FORCES a normalised
/// joint, which is what makes the predicate usable as a hypothesis: a
/// downstream theorem may assume `KIndependent` without separately assuming
/// that `W` is a distribution.
fn declare_sum_maps_one_of_k_independent(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let map_t = map_ty(d);
    let fam = fam_ty(d);
    let cty = coef_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);

    let ki_ty = d.const_app(p.product_space.k_independent, &[m, n, pp, w]);
    let ki_fv = d.fresh_fvar();
    let ki = d.kernel().fvar(ki_fv);

    let marg_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let pi = d.apply(pp, &[i]);
        let s = rsum_range(d, p, pi, n);
        let one_r = rone(d, p);
        let body = req(d, s, one_r);
        d.pi_fv(i_fv, nat, body)
    };
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    // f i k := one.
    let ones_family = {
        let i_fv = d.fresh_fvar();
        let k_fv = d.fresh_fvar();
        let one_r = rone(d, p);
        let over_k = d.lam_fv(k_fv, nat, one_r);
        d.lam_fv(i_fv, nat, over_k)
    };
    let ones = const_one(d, p);
    let one_r = rone(d, p);

    // The instantiated hypothesis, whose two sides are the two ends below.
    let instance = d.apply(ki, &[ones_family]);

    // LEFT: expectationMaps m n (prod_var ones_family m) W, i.e.
    // sumMaps m n (fun g => prodRange (fun i => one) m * W g).
    let heavy = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let inner = along(d, ones_family, g);
        let head = rprod_range(d, p, inner, m);
        let wg = d.apply(w, &[g]);
        let body = rmul(d, head, wg);
        d.lam_fv(g_fv, map_t, body)
    };
    let heavy_sum = rsum_maps(d, p, m, n, heavy);
    let bare_sum = rsum_maps(d, p, m, n, w);

    // sumMaps m n heavy = sumMaps m n W, pointwise.
    let strip = {
        let pointwise = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let inner = along(d, ones_family, g);
            let head = rprod_range(d, p, inner, m);
            let wg = d.apply(w, &[g]);
            let start = rmul(d, head, wg);
            let mid = rmul(d, one_r, wg);
            let collapse = d.lemma(p.product_space.prod_range_one, &[m]);
            let s1 = rcongr(d, head, one_r, collapse, &|d, t| rmul(d, t, wg));
            let s2 = one_mul(d, p, wg);
            let (_, chained) = rchain(d, start, &[(mid, s1), (wg, s2)]);
            d.lam_fv(g_fv, map_t, chained)
        };
        d.lemma(p.sum_maps_congr, &[n, m, heavy, w, pointwise])
    };

    // RIGHT: prodRange (fun i => expectation (fun _ => one) (P i) n) m = one.
    let marg = marginal_expectations(d, p, ones_family, pp, n);
    let marg_prod = rprod_range(d, p, marg, m);
    let ones_prod = rprod_range(d, p, ones, m);
    let each_marginal = {
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let pi = d.apply(pp, &[i]);
            // expectation (fun _ => one) (P i) n ≡ sumRange (fun k => one * P i k) n
            let scaled = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let pik = d.apply(pi, &[k]);
                let body = rmul(d, one_r, pik);
                d.lam_fv(k_fv, nat, body)
            };
            let scaled_sum = rsum_range(d, p, scaled, n);
            let plain_sum = rsum_range(d, p, pi, n);
            let per_k = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let pik = d.apply(pi, &[k]);
                let body = one_mul(d, p, pik);
                d.lam_fv(k_fv, nat, body)
            };
            let s1 = d.lemma(p.sum_range_congr, &[scaled, pi, n, per_k]);
            let s2 = d.apply(hm, &[i]);
            let (_, chained) = rchain(d, scaled_sum, &[(plain_sum, s1), (one_r, s2)]);
            d.lam_fv(i_fv, nat, chained)
        };
        d.lemma(p.prod_range_congr, &[marg, ones, m, pointwise])
    };
    let finish = d.lemma(p.product_space.prod_range_one, &[m]);

    let back = rsymm(d, heavy_sum, bare_sum, strip);
    let (_, proof) = rchain(
        d,
        bare_sum,
        &[
            (heavy_sum, back),
            (marg_prod, instance),
            (ones_prod, each_marginal),
            (one_r, finish),
        ],
    );

    let stmt = req(d, bare_sum, one_r);
    let ty = {
        let with_hm = d.arrow(marg_ty, stmt);
        let with_ki = d.arrow(ki_ty, with_hm);
        let over_w = d.pi_fv(w_fv, fam, with_ki);
        let over_pp = d.pi_fv(pp_fv, cty, over_w);
        let over_m = d.pi_fv(m_fv, nat, over_pp);
        d.pi_fv(n_fv, nat, over_m)
    };
    let value = {
        let with_hm = d.lam_fv(hm_fv, marg_ty, proof);
        let with_ki = d.lam_fv(ki_fv, ki_ty, with_hm);
        let over_w = d.lam_fv(w_fv, fam, with_ki);
        let over_pp = d.lam_fv(pp_fv, cty, over_w);
        let over_m = d.lam_fv(m_fv, nat, over_pp);
        d.lam_fv(n_fv, nat, over_m)
    };
    d.declare_theorem(p.product_space.sum_maps_one_of_k_independent, ty, value)
}

#[cfg(test)]
#[path = "product_space_tests.rs"]
mod product_space_tests;
