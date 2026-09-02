//! `Rat.prodRange` and `Rat.sumMaps` — a finite product over a range and a
//! finite sum **indexed by a function space**, over ℚ.
//!
//! Both are ports of the `Int` originals (`int_prelude/prod.rs`,
//! `int_prelude/sum_maps.rs`), and they exist for one reason: ADR-1440's
//! **obligation 1** toward `Rat.det_mul` expands `det (A·B) n` in the rows of
//! `A·B` by `Rat.det_row_multilinear` once per row, and the result is a sum
//! indexed by every map `[0,n) -> [0,n)` whose coefficient is a product over
//! the rows. Neither aggregate existed over ℚ — measured absent by
//! `shape_search --name-like Rat.sumMaps` / `--name-like Rat.prodRange`
//! against a fresh 2,048-declaration index, with `Int.sumMaps` (5 rows),
//! `Int.prodRange` and `Rat.sumRange` as positive controls.
//!
//! The construction is the `Int` one verbatim in shape:
//!
//! ```text
//! prodRange f 0        = 1
//! prodRange f (m + 1)  = prodRange f m * f m
//!
//! sumMaps 0       n F  = F (fun _ => 0)
//! sumMaps (m + 1) n F  = sumRange (fun k => sumMaps m n (fun g => F (cons k g))) n
//! ```
//!
//! where `cons k g` is the `Nat -> Nat` that is `k` at `0` and `g (i - 1)`
//! after, built inline as a `Nat.rec` so **both** of its equations hold by
//! ι-reduction alone — no `Nat.beq`, no `bool_select_nat`, no ordering lemma.
//! `sumMaps`'s motive is `fun _ : Nat => ((Nat -> Nat) -> Rat) -> Rat`,
//! constant in the index and *not* `Rat`, the same higher-order trick
//! `Rat.det` already uses.
//!
//! What is new relative to `Int`: this prelude has **no `Rat.one_mul` and no
//! `Rat.zero_mul`** (only `mul_one` and `mul_zero`), so every base case that
//! wants a left identity or a left absorbing zero derives it inline from
//! `Rat.mul_comm` — see [`one_mul_proof`] and [`zero_eq_zero_mul_proof`]. And
//! the right-distributive law is `Rat.right_distrib`, not `Int.add_mul`.
//!
//! The definitions' correctness is checked by **evaluation**, not by the
//! trusted gate — `(Nat -> Rat) -> Nat -> Rat` is that type whatever the
//! function returns. See `sum_maps_tests.rs`.

use super::RatPrelude;
use super::ops::{
    radd, rat_ty, rchain, rcongr, req, rmul, rone, rrefl, rsum_range, rsymm, rtrans, rzero,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.prodRange`: above `Rat.mul`/`Rat.one`
/// (`rat_prelude::defs`'s `LEAF_HEIGHT` 30 / `DERIVED_HEIGHT` 31) and above
/// `Rat.sumRange` (34), following the "outranks everything it unfolds to"
/// convention.
const PROD_RANGE_HEIGHT: u16 = 35;

/// Delta height for `Rat.sumMaps`: one above [`PROD_RANGE_HEIGHT`] and two
/// above `Rat.sumRange`, which it unfolds to.
const SUM_MAPS_HEIGHT: u16 = 36;

/// Declare `Rat.prodRange`, `Rat.sumMaps` and everything this file proves.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sum_maps_all(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_prod_range(d, p)?;
    declare_prod_range_equations(d, p)?;
    declare_prod_range_shift_front(d, p)?;
    declare_prod_range_congr(d, p)?;
    declare_sum_range_mul_right(d, p)?;
    declare_sum_range_mul_left(d, p)?;
    declare_sum_maps(d, p)?;
    declare_sum_maps_equations(d, p)?;
    declare_sum_maps_congr(d, p)?;
    declare_sum_maps_mul_left(d, p)?;
    declare_sum_maps_mul_right(d, p)?;
    Ok(())
}

// --- shared shapes ---------------------------------------------------------

/// `(Nat -> Nat) -> Rat`, the type of a summand indexed by a map.
pub(super) fn fam_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_nat = d.arrow(nat, nat);
    d.arrow(fn_nat, carrier)
}

/// `Nat -> Nat`, the type of an index map.
pub(super) fn map_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `Nat -> Rat`, the type of a range-indexed family.
fn seq_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    d.arrow(nat, carrier)
}

/// `cons k g : Nat -> Nat` — `k` at index `0`, `g j` at index `succ j`.
///
/// Built inline as `fun i => Nat.rec.{1} (fun _ => Nat) k (fun j _ => g j) i`
/// so that **both** equations hold by ι-reduction alone. Deliberately NOT a
/// declared definition: it appears only inside `Rat.sumMaps`'s own body and
/// inside proofs about it, so naming it would add a delta height and a name
/// to the shared `Nat` namespace for no reuse.
pub(super) fn cons_fn(d: &mut IntDev<'_>, k: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let gj = d.apply(g, &[j]);
        let inner = d.lam_fv(ih_fv, nat, gj);
        d.lam_fv(j_fv, nat, inner)
    };
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, k, minor_succ, i]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun _ : Nat => Nat.zero` — the junk map the empty sum is evaluated at.
///
/// Any total `Nat -> Nat` would do: `sumMaps 0 n F` is `F` applied to *some*
/// map, and the only consumer is a `prodRange _ 0`, which does not look at it.
pub(super) fn junk_map(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let zero = d.zero();
    d.kernel().lam(anon, nat, zero, BinderInfo::Default)
}

/// `Rat.prodRange` applied at `f`, `n`.
pub(super) fn rprod_range(d: &mut IntDev<'_>, p: RatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.prod_range, &[f, n])
}

/// `Rat.sumMaps` applied at `m`, `n`, `f`.
pub(super) fn rsum_maps(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    n: ExprId,
    f: ExprId,
) -> ExprId {
    d.const_app(p.sum_maps, &[m, n, f])
}

/// `Eq Rat (mul one a) a`, derived from `mul_comm` and `mul_one`.
///
/// This prelude declares `Rat.mul_one` and not `Rat.one_mul`; every base case
/// below that needs the left identity goes through here rather than through a
/// new declaration in the shared `Rat` namespace.
fn one_mul_proof(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId) -> ExprId {
    let one_r = rone(d, p);
    let lhs = rmul(d, one_r, a);
    let mid = rmul(d, a, one_r);
    let comm = d.lemma(p.mul_comm, &[one_r, a]);
    let mo = d.lemma(p.mul_one, &[a]);
    rtrans(d, lhs, mid, a, comm, mo)
}

/// `Eq Rat zero (mul zero z)` — the **reversed** direction on purpose.
///
/// At `n = 0` the `sumRange_mul_right` induction's goal is
/// `sumRange _ 0 = mul (sumRange f 0) z`, whose left side reduces to `zero`
/// and whose right side to `mul zero z`; the natural reading
/// `mul zero z = zero` is the wrong way round for it.
fn zero_eq_zero_mul_proof(d: &mut IntDev<'_>, p: RatPrelude, z: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let lhs = rmul(d, zero_r, z);
    let mid = rmul(d, z, zero_r);
    let comm = d.lemma(p.mul_comm, &[zero_r, z]);
    let mz = d.lemma(p.mul_zero, &[z]);
    let fwd = rtrans(d, lhs, mid, zero_r, comm, mz);
    rsymm(d, lhs, zero_r, fwd)
}

// --- Rat.prodRange ---------------------------------------------------------

/// Admit `Rat.prodRange : (Nat -> Rat) -> Nat -> Rat` by structural recursion
/// on the `Nat` bound: `prodRange f zero ≡ Rat.one`,
/// `prodRange f (succ n) ≡ Rat.mul (prodRange f n) (f n)`.
fn declare_prod_range(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = seq_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = rone(d, p);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = rmul(d, ih, fj);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, carrier);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.prod_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PROD_RANGE_HEIGHT),
    })
}

/// `Rat.prodRange_zero` / `Rat.prodRange_succ`, each an `Eq.refl` at `Rat` —
/// `Rat.prodRange` computes on both minor premises.
fn declare_prod_range_equations(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let fn_ty = seq_ty(d);

    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = rprod_range(d, p, f, zero_n);
        let one_r = rone(d, p);
        let stmt = req(d, lhs, one_r);
        let proof = rrefl(d, one_r);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.prod_range_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = rprod_range(d, p, f, sn);
        let prior = rprod_range(d, p, f, n);
        let fn_at = d.apply(f, &[n]);
        let rhs = rmul(d, prior, fn_at);
        let stmt = req(d, lhs, rhs);
        let proof = rrefl(d, rhs);
        let ty = {
            let inner = d.pi_fv(n_fv, nat, stmt);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.prod_range_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Rat.prodRange_shiftFront : ∀ f n, prodRange f (succ n) =
/// f 0 * prodRange (fun k => f (succ k)) n` — peel the FRONT factor.
///
/// `prodRange_succ` already peels the BACK factor for free. Induction on `n`;
/// the base case needs a `one_mul`/`mul_one` pair (`Rat.mul` does not reduce
/// definitionally on a symbolic argument), and the successor step is one
/// `Rat.mul_assoc` after the induction hypothesis.
fn declare_prod_range_shift_front(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let fn_ty = seq_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let shifted_of = |d: &mut IntDev<'_>, f: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = d.apply(f, &[sk]);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let lhs = rprod_range(d, p, f, sx);
        let zero_n = d.zero();
        let f0 = d.apply(f, &[zero_n]);
        let shifted_f = shifted_of(d, f);
        let pr = rprod_range(d, p, shifted_f, x);
        let rhs = rmul(d, f0, pr);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let f0 = d.apply(f, &[zero_n]);
            let one_r = rone(d, p);
            let mul_one_f0 = rmul(d, one_r, f0);
            let step1 = one_mul_proof(d, p, f0);
            let mul_f0_one = rmul(d, f0, one_r);
            let step2 = d.lemma(p.mul_one, &[f0]);
            let step2_rev = rsymm(d, mul_f0_one, f0, step2);
            rtrans(d, mul_one_f0, f0, mul_f0_one, step1, step2_rev)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let f_prior_succ = rprod_range(d, p, f, sj);
            let f_sj = d.apply(f, &[sj]);
            let start = rmul(d, f_prior_succ, f_sj);

            let zero_n = d.zero();
            let f0 = d.apply(f, &[zero_n]);
            let shifted_f = shifted_of(d, f);
            let shifted_j = rprod_range(d, p, shifted_f, j);
            let mid1 = rmul(d, f0, shifted_j);
            let h1 = rcongr(d, f_prior_succ, mid1, ih, &|d, t| rmul(d, t, f_sj));
            let after_ih = rmul(d, mid1, f_sj);

            let inner = rmul(d, shifted_j, f_sj);
            let end_ = rmul(d, f0, inner);
            let h2 = d.lemma(p.mul_assoc, &[f0, shifted_j, f_sj]);

            let (_e, proof) = rchain(d, start, &[(after_ih, h1), (end_, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.prod_range_shift_front,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.prodRange_congr : ∀ f g n, (∀ k, f k = g k) →
/// prodRange f n = prodRange g n`.
fn declare_prod_range_congr(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let fn_ty = seq_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let eq = req(d, fk, gk);
        d.pi_fv(k_fv, nat, eq)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = rprod_range(d, p, f, x);
        let rhs = rprod_range(d, p, g, x);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let one_r = rone(d, p);
            rrefl(d, one_r)
        },
        &|d, j, ih| {
            let f_prior = rprod_range(d, p, f, j);
            let g_prior = rprod_range(d, p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = rmul(d, f_prior, fj);
            let mid = rmul(d, g_prior, fj);
            let h1 = rcongr(d, f_prior, g_prior, ih, &|d, t| rmul(d, t, fj));
            let end_ = rmul(d, g_prior, gj);
            let pointwise_j = d.apply(h, &[j]);
            let h2 = rcongr(d, fj, gj, pointwise_j, &|d, t| rmul(d, g_prior, t));
            let (_, proof) = rchain(d, start, &[(mid, h1), (end_, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let with_h = d.pi_fv(h_fv, pointwise, stmt);
        let over_n = d.pi_fv(n_fv, nat, with_h);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, pointwise, proof);
        let over_n = d.lam_fv(n_fv, nat, with_h);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.prod_range_congr,
        uparams: vec![],
        ty,
        value,
    })
}

// --- pulling a constant out of a Rat.sumRange ------------------------------

/// `Rat.sumRange_mul_right : ∀ f z n,
/// sumRange (fun k => f k * z) n = sumRange f n * z`.
///
/// `Rat.mul_sumRange` is the LEFT companion but states the pull the other way
/// round (`c * sumRange f n = sumRange (fun i => c * f i) n`); the `sumMaps`
/// induction needs both directions and both sides, so the two forms are
/// declared here in the `Int.sumRange_mul_*` orientation.
fn declare_sum_range_mul_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = seq_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let body = rmul(d, fk, z);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = rsum_range(d, p, scaled, x);
        let prior = rsum_range(d, p, f, x);
        let rhs = rmul(d, prior, z);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| zero_eq_zero_mul_proof(d, p, z),
        &|d, j, ih| {
            let prior_scaled = rsum_range(d, p, scaled, j);
            let prior = rsum_range(d, p, f, j);
            let fj = d.apply(f, &[j]);
            let term = rmul(d, fj, z);
            let start = radd(d, prior_scaled, term);
            let scaled_prior = rmul(d, prior, z);
            let mid = radd(d, scaled_prior, term);
            let h1 = rcongr(d, prior_scaled, scaled_prior, ih, &|d, t| radd(d, t, term));
            let sum_succ = radd(d, prior, fj);
            let end_ = rmul(d, sum_succ, z);
            let dist = d.lemma(p.right_distrib, &[prior, fj, z]);
            let h2 = rsymm(d, end_, mid, dist);
            let (_, proof) = rchain(d, start, &[(mid, h1), (end_, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_z = d.pi_fv(z_fv, carrier, over_n);
        d.pi_fv(f_fv, fn_ty, over_z)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_z = d.lam_fv(z_fv, carrier, over_n);
        d.lam_fv(f_fv, fn_ty, over_z)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_mul_right,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.sumRange_mul_left : ∀ z f n,
/// sumRange (fun k => z * f k) n = z * sumRange f n`.
fn declare_sum_range_mul_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = seq_ty(d);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let body = rmul(d, z, fk);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = rsum_range(d, p, scaled, x);
        let prior = rsum_range(d, p, f, x);
        let rhs = rmul(d, z, prior);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_r = rzero(d, p);
            let mz = d.lemma(p.mul_zero, &[z]);
            let lhs = rmul(d, z, zero_r);
            rsymm(d, lhs, zero_r, mz)
        },
        &|d, j, ih| {
            let prior_scaled = rsum_range(d, p, scaled, j);
            let prior = rsum_range(d, p, f, j);
            let fj = d.apply(f, &[j]);
            let term = rmul(d, z, fj);
            let start = radd(d, prior_scaled, term);
            let scaled_prior = rmul(d, z, prior);
            let mid = radd(d, scaled_prior, term);
            let h1 = rcongr(d, prior_scaled, scaled_prior, ih, &|d, t| radd(d, t, term));
            let sum_succ = radd(d, prior, fj);
            let end_ = rmul(d, z, sum_succ);
            let dist = d.lemma(p.left_distrib, &[z, prior, fj]);
            let h2 = rsymm(d, end_, mid, dist);
            let (_, proof) = rchain(d, start, &[(mid, h1), (end_, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_f = d.pi_fv(f_fv, fn_ty, over_n);
        d.pi_fv(z_fv, carrier, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_f = d.lam_fv(f_fv, fn_ty, over_n);
        d.lam_fv(z_fv, carrier, over_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_mul_left,
        uparams: vec![],
        ty,
        value,
    })
}

// --- Rat.sumMaps -----------------------------------------------------------

/// Admit `Rat.sumMaps : Nat -> Nat -> ((Nat -> Nat) -> Rat) -> Rat`.
///
/// Structural recursion on the FIRST argument with the higher-order motive
/// `fun _ : Nat => ((Nat -> Nat) -> Rat) -> Rat`; see the module doc.
fn declare_sum_maps(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fam = fam_ty(d);
    let map_t = map_ty(d);
    let fam_to_rat = d.arrow(fam, carrier);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = d.kernel().lam(anon, nat, fam_to_rat, BinderInfo::Default);

    let minor_zero = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let junk = junk_map(d);
        let body = d.apply(f, &[junk]);
        d.lam_fv(f_fv, fam, body)
    };

    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        let summand = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let shifted = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let c = cons_fn(d, k, g);
                let body = d.apply(f, &[c]);
                d.lam_fv(g_fv, map_t, body)
            };
            let body = d.apply(ih, &[shifted]);
            d.lam_fv(k_fv, nat, body)
        };
        let body = rsum_range(d, p, summand, n);
        let over_f = d.lam_fv(f_fv, fam, body);
        let over_ih = d.lam_fv(ih_fv, fam_to_rat, over_f);
        d.lam_fv(j_fv, nat, over_ih)
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let rec_app = d.apply(rec, &[motive, minor_zero, minor_succ, m]);

    let f_outer_fv = d.fresh_fvar();
    let f_outer = d.kernel().fvar(f_outer_fv);
    let applied = d.apply(rec_app, &[f_outer]);

    let value = {
        let over_f = d.lam_fv(f_outer_fv, fam, applied);
        let over_n = d.lam_fv(n_fv, nat, over_f);
        d.lam_fv(m_fv, nat, over_n)
    };
    let ty = {
        let over_f = d.arrow(fam, carrier);
        let over_n = d.arrow(nat, over_f);
        d.arrow(nat, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_maps,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SUM_MAPS_HEIGHT),
    })
}

/// The defining equations `Rat.sumMaps_zero` and `Rat.sumMaps_succ`, each an
/// `Eq.refl` at `Rat` — `Rat.sumMaps` computes on both minor premises.
fn declare_sum_maps_equations(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let fam = fam_ty(d);
    let map_t = map_ty(d);

    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = rsum_maps(d, p, zero_n, n, f);
        let junk = junk_map(d);
        let rhs = d.apply(f, &[junk]);
        let stmt = req(d, lhs, rhs);
        let proof = rrefl(d, rhs);
        let ty = {
            let over_f = d.pi_fv(f_fv, fam, stmt);
            d.pi_fv(n_fv, nat, over_f)
        };
        let value = {
            let over_f = d.lam_fv(f_fv, fam, proof);
            d.lam_fv(n_fv, nat, over_f)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_maps_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        let sm = d.succ(m);
        let lhs = rsum_maps(d, p, sm, n, f);
        let summand = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let shifted = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let c = cons_fn(d, k, g);
                let body = d.apply(f, &[c]);
                d.lam_fv(g_fv, map_t, body)
            };
            let body = rsum_maps(d, p, m, n, shifted);
            d.lam_fv(k_fv, nat, body)
        };
        let rhs = rsum_range(d, p, summand, n);
        let stmt = req(d, lhs, rhs);
        let proof = rrefl(d, rhs);
        let ty = {
            let over_f = d.pi_fv(f_fv, fam, stmt);
            let over_n = d.pi_fv(n_fv, nat, over_f);
            d.pi_fv(m_fv, nat, over_n)
        };
        let value = {
            let over_f = d.lam_fv(f_fv, fam, proof);
            let over_n = d.lam_fv(n_fv, nat, over_f);
            d.lam_fv(m_fv, nat, over_n)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_maps_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Rat.sumMaps_congr : ∀ n m F G, (∀ g, F g = G g) →
/// sumMaps m n F = sumMaps m n G`.
///
/// Induction on `m` with the motive quantified over BOTH `F` and `G`: the
/// successor step applies the induction hypothesis at
/// `fun g => F (cons k g)` / `fun g => G (cons k g)`, a different pair.
fn declare_sum_maps_congr(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let fam = fam_ty(d);
    let map_t = map_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let pointwise = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let fa = d.apply(f, &[a]);
            let ga = d.apply(gg, &[a]);
            let eq = req(d, fa, ga);
            d.pi_fv(a_fv, map_t, eq)
        };
        let lhs = rsum_maps(d, p, x, n, f);
        let rhs = rsum_maps(d, p, x, n, gg);
        let concl = req(d, lhs, rhs);
        let with_h = d.arrow(pointwise, concl);
        let over_g = d.pi_fv(g_fv, fam, with_h);
        d.pi_fv(f_fv, fam, over_g)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let g_fv = d.fresh_fvar();
            let gg = d.kernel().fvar(g_fv);
            let pointwise = {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let fa = d.apply(f, &[a]);
                let ga = d.apply(gg, &[a]);
                let eq = req(d, fa, ga);
                d.pi_fv(a_fv, map_t, eq)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let junk = junk_map(d);
            let body = d.apply(h, &[junk]);
            let with_h = d.lam_fv(h_fv, pointwise, body);
            let over_g = d.lam_fv(g_fv, fam, with_h);
            d.lam_fv(f_fv, fam, over_g)
        },
        &|d, j, ih| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let g_fv = d.fresh_fvar();
            let gg = d.kernel().fvar(g_fv);
            let pointwise = {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let fa = d.apply(f, &[a]);
                let ga = d.apply(gg, &[a]);
                let eq = req(d, fa, ga);
                d.pi_fv(a_fv, map_t, eq)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let shift = |d: &mut IntDev<'_>, target: ExprId, k: ExprId| -> ExprId {
                let map_t = map_ty(d);
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let c = cons_fn(d, k, a);
                let body = d.apply(target, &[c]);
                d.lam_fv(a_fv, map_t, body)
            };

            let summand_lhs = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sf = shift(d, f, k);
                let body = rsum_maps(d, p, j, n, sf);
                d.lam_fv(k_fv, nat, body)
            };
            let summand_rhs = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sg = shift(d, gg, k);
                let body = rsum_maps(d, p, j, n, sg);
                d.lam_fv(k_fv, nat, body)
            };
            let per_k = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sf = shift(d, f, k);
                let sg = shift(d, gg, k);
                let inner_h = {
                    let map_t = map_ty(d);
                    let a_fv = d.fresh_fvar();
                    let a = d.kernel().fvar(a_fv);
                    let c = cons_fn(d, k, a);
                    let body = d.apply(h, &[c]);
                    d.lam_fv(a_fv, map_t, body)
                };
                let body = d.apply(ih, &[sf, sg, inner_h]);
                d.lam_fv(k_fv, nat, body)
            };
            let congr = d.lemma(p.sum_range_congr, &[summand_lhs, summand_rhs, n, per_k]);
            let with_h = d.lam_fv(h_fv, pointwise, congr);
            let over_g = d.lam_fv(g_fv, fam, with_h);
            d.lam_fv(f_fv, fam, over_g)
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
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_maps_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.sumMaps_mul_left : ∀ n z m H,
/// sumMaps m n (fun g => z * H g) = z * sumMaps m n H`.
fn declare_sum_maps_mul_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fam = fam_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let scale = |d: &mut IntDev<'_>, hh: ExprId| -> ExprId {
        let map_t = map_ty(d);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let ha = d.apply(hh, &[a]);
        let body = rmul(d, z, ha);
        d.lam_fv(a_fv, map_t, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let h_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(h_fv);
        let scaled = scale(d, hh);
        let lhs = rsum_maps(d, p, x, n, scaled);
        let prior = rsum_maps(d, p, x, n, hh);
        let rhs = rmul(d, z, prior);
        let eq = req(d, lhs, rhs);
        d.pi_fv(h_fv, fam, eq)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let h_fv = d.fresh_fvar();
            let hh = d.kernel().fvar(h_fv);
            let junk = junk_map(d);
            let h_junk = d.apply(hh, &[junk]);
            let body = rmul(d, z, h_junk);
            let refl = rrefl(d, body);
            d.lam_fv(h_fv, fam, refl)
        },
        &|d, j, ih| {
            let h_fv = d.fresh_fvar();
            let hh = d.kernel().fvar(h_fv);

            let shift = |d: &mut IntDev<'_>, target: ExprId, k: ExprId| -> ExprId {
                let map_t = map_ty(d);
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let c = cons_fn(d, k, a);
                let body = d.apply(target, &[c]);
                d.lam_fv(a_fv, map_t, body)
            };

            let inner_scaled = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let sc = scale(d, sh);
                let body = rsum_maps(d, p, j, n, sc);
                d.lam_fv(k_fv, nat, body)
            };
            let inner_plain = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let prior = rsum_maps(d, p, j, n, sh);
                let body = rmul(d, z, prior);
                d.lam_fv(k_fv, nat, body)
            };
            let per_k = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let body = d.apply(ih, &[sh]);
                d.lam_fv(k_fv, nat, body)
            };
            let start = rsum_range(d, p, inner_scaled, n);
            let mid = rsum_range(d, p, inner_plain, n);
            let h1 = d.lemma(p.sum_range_congr, &[inner_scaled, inner_plain, n, per_k]);

            let bare = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let body = rsum_maps(d, p, j, n, sh);
                d.lam_fv(k_fv, nat, body)
            };
            let bare_sum = rsum_range(d, p, bare, n);
            let end_ = rmul(d, z, bare_sum);
            let h2 = d.lemma(p.sum_range_mul_left, &[z, bare, n]);
            let (_, chained) = rchain(d, start, &[(mid, h1), (end_, h2)]);
            d.lam_fv(h_fv, fam, chained)
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        let over_z = d.pi_fv(z_fv, carrier, over_m);
        d.pi_fv(n_fv, nat, over_z)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_z = d.lam_fv(z_fv, carrier, over_m);
        d.lam_fv(n_fv, nat, over_z)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_maps_mul_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.sumMaps_mul_right : ∀ n z m H,
/// sumMaps m n (fun g => H g * z) = sumMaps m n H * z`.
///
/// The mirror of [`declare_sum_maps_mul_left`]. It is what pulls the whole
/// `det B n` factor out of the Cauchy–Binet sum once `Rat.det_row_selection`
/// has put it on the RIGHT of every summand.
fn declare_sum_maps_mul_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fam = fam_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let scale = |d: &mut IntDev<'_>, hh: ExprId| -> ExprId {
        let map_t = map_ty(d);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let ha = d.apply(hh, &[a]);
        let body = rmul(d, ha, z);
        d.lam_fv(a_fv, map_t, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let h_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(h_fv);
        let scaled = scale(d, hh);
        let lhs = rsum_maps(d, p, x, n, scaled);
        let prior = rsum_maps(d, p, x, n, hh);
        let rhs = rmul(d, prior, z);
        let eq = req(d, lhs, rhs);
        d.pi_fv(h_fv, fam, eq)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let h_fv = d.fresh_fvar();
            let hh = d.kernel().fvar(h_fv);
            let junk = junk_map(d);
            let h_junk = d.apply(hh, &[junk]);
            let body = rmul(d, h_junk, z);
            let refl = rrefl(d, body);
            d.lam_fv(h_fv, fam, refl)
        },
        &|d, j, ih| {
            let h_fv = d.fresh_fvar();
            let hh = d.kernel().fvar(h_fv);

            let shift = |d: &mut IntDev<'_>, target: ExprId, k: ExprId| -> ExprId {
                let map_t = map_ty(d);
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let c = cons_fn(d, k, a);
                let body = d.apply(target, &[c]);
                d.lam_fv(a_fv, map_t, body)
            };

            let inner_scaled = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let sc = scale(d, sh);
                let body = rsum_maps(d, p, j, n, sc);
                d.lam_fv(k_fv, nat, body)
            };
            let inner_plain = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let prior = rsum_maps(d, p, j, n, sh);
                let body = rmul(d, prior, z);
                d.lam_fv(k_fv, nat, body)
            };
            let per_k = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let body = d.apply(ih, &[sh]);
                d.lam_fv(k_fv, nat, body)
            };
            let start = rsum_range(d, p, inner_scaled, n);
            let mid = rsum_range(d, p, inner_plain, n);
            let h1 = d.lemma(p.sum_range_congr, &[inner_scaled, inner_plain, n, per_k]);

            let bare = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let body = rsum_maps(d, p, j, n, sh);
                d.lam_fv(k_fv, nat, body)
            };
            let bare_sum = rsum_range(d, p, bare, n);
            let end_ = rmul(d, bare_sum, z);
            let h2 = d.lemma(p.sum_range_mul_right, &[bare, z, n]);
            let (_, chained) = rchain(d, start, &[(mid, h1), (end_, h2)]);
            d.lam_fv(h_fv, fam, chained)
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        let over_z = d.pi_fv(z_fv, carrier, over_m);
        d.pi_fv(n_fv, nat, over_z)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_z = d.lam_fv(z_fv, carrier, over_m);
        d.lam_fv(n_fv, nat, over_z)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_maps_mul_right,
        uparams: vec![],
        ty,
        value,
    })
}
