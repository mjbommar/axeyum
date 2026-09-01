//! `Int.sumRange : (Nat → Int) → Nat → Int` — the **signed** finite sum, the
//! aggregate ADR-1260 named as the single obstruction between the landed
//! lattice-point partition and Eisenstein's lemma.
//!
//! The `Int` prelude folded products only. `Int.prodRange` (`prod.rs`) exists
//! because Wilson's theorem and Euler's totient theorem both multiply; nothing
//! in this development had ever needed to *subtract inside a finite sum*, which
//! is exactly what Eisenstein's `(a−1)·Σk = p·(F+N) − 2·Σ_neg` does. `Nat` and
//! `Rat` both have `sumRange`; `Int` did not. This is a missing construction
//! over an existing carrier, not a missing carrier.
//!
//! Convention, matching `Nat.sumRange`
//! (`nat_prelude/defs.rs::declare_finite_ranges`) and `Int.prodRange` exactly:
//! the bound is **exclusive**, the base case is the identity of the operation
//! (`Int.zero`, where `prodRange` uses `Int.one`), and the successor step adds
//! the fresh term onto the **right** of the prior sum
//! (`sumRange f (succ n) ≡ add (sumRange f n) (f n)`).
//!
//! # What transported from `prod.rs` and what did not
//!
//! The construction, its two defining equations and `sumRange_congr` are the
//! same inductions with `Int.mul`/`Int.one` replaced by `Int.add`/`Int.zero`.
//! Three things are genuinely different, and none of them is a style choice:
//!
//! * **`modEq_sumRange` carries NO `0 < n` hypothesis**, while
//!   `modEq_prodRange` does. `prodRange`'s step needs `Int.ModEq.mul`, whose
//!   own statement here is positivity-scoped; the sum's step needs
//!   `Int.ModEq.add_right`/`add_left`, both of which this prelude proves
//!   UNCONDITIONALLY in the modulus. Transporting the hypothesis would have
//!   weakened the lemma for no reason — the mod-2 reader Eisenstein wants would
//!   then have had to discharge `0 < 2` at every use.
//! * **The base cases compute.** `Int.mul` reduces on neither operand when both
//!   are symbolic, so `prodRange_mul`'s base needs an explicit `Int.mul_one`.
//!   Here both operands of the base are the literal `Int.zero ≡ Int.ofNat 0`,
//!   so `Int.add zero zero` δι-reduces to `zero`.
//! * **`sumRange_sub` needs no induction at all.** `Int.sub a b := add a (neg b)`
//!   is a plain `Definition`, so `sumRange (fun k => sub (f k) (g k)) n` is
//!   definitionally `sumRange (fun k => add (f k) (neg (g k))) n`, and the
//!   lemma falls out of `sumRange_add` composed with `sumRange_neg`.
//!   `prodRange` has no analogue, because `Int` has no multiplicative inverse
//!   to fold.
//!
//! # Retrieval note
//!
//! [`super::modeq::neg_add`] already existed, private, built inline for
//! `declare_modeq_add_right`'s cancellation — hiding place 2 in the retrieval
//! taxonomy. It is the whole content of `sumRange_neg`'s step and is reused
//! here rather than re-derived; it is now also exposed as the public theorem
//! `Int.neg_add`, which the prelude had never stated.

use super::defs::POW_HEIGHT;
use super::modeq::neg_add;
use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Delta height for `Int.sumRange`. Equal to `Int.prodRange`'s
/// (`POW_HEIGHT + 1`): the two fold the same shape over the same carrier,
/// neither calls the other, and both call only `Int.add`/`Int.mul` at
/// `DERIVED_HEIGHT`.
const SUM_RANGE_HEIGHT: u16 = POW_HEIGHT + 1;

/// Admit `Int.sumRange : (Nat → Int) → Nat → Int` by structural recursion on
/// the `Nat` bound:
///
/// `sumRange f Nat.zero ≡ Int.zero`,
/// `sumRange f (Nat.succ n) ≡ Int.add (sumRange f n) (f n)`.
///
/// Same `Nat.rec` skeleton as [`super::prod::declare_prod_range`] — a constant
/// `fun _ => Int` motive, `NatPrelude::rec` rather than `Int.rec` — with the
/// monoid swapped.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_sum_range(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();

    let fn_ty = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, int_ty, BinderInfo::Default);
    let minor_zero = d.izero();
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = d.iadd(ih, fj);
        let inner = d.lam_fv(ih_fv, int_ty, body);
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
        let over_n = d.arrow(nat, int_ty);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SUM_RANGE_HEIGHT),
    })
}

/// The defining equations `Int.sumRange_zero` and `Int.sumRange_succ`, each an
/// `Eq.refl` at `Int` — `Int.sumRange` computes on both minor premises.
///
/// # Errors
///
/// Returns the kernel's rejection if a generated proof does not check.
pub(super) fn declare_sum_range_equations(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    // sumRange_zero : ∀ (f : Nat → Int), Eq Int (sumRange f zero) zero.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.sum_range, &[f, zero_n]);
        let zero_i = d.izero();
        let stmt = d.ieq(lhs, zero_i);
        let proof = d.irefl(zero_i);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        d.declare_theorem(p.sum_range_zero, ty, value)?;
    }

    // sumRange_succ :
    //   ∀ (f : Nat → Int) (n : Nat),
    //     Eq Int (sumRange f (succ n)) (add (sumRange f n) (f n)).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let sn = d.succ(n);
        let lhs = d.const_app(p.sum_range, &[f, sn]);
        let prior = d.const_app(p.sum_range, &[f, n]);
        let fn_ = d.apply(f, &[n]);
        let rhs = d.iadd(prior, fn_);
        let stmt = d.ieq(lhs, rhs);
        let proof = d.irefl(rhs);

        let ty = {
            let with_n = d.pi_fv(n_fv, nat, stmt);
            d.pi_fv(f_fv, fn_ty, with_n)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        d.declare_theorem(p.sum_range_succ, ty, value)?;
    }
    Ok(())
}

/// `Int.neg_add : ∀ a b, Eq Int (neg (add a b)) (add (neg a) (neg b))` —
/// negation distributes over addition.
///
/// The proof term already existed as `modeq.rs`'s private `neg_add` helper
/// (built inline for `declare_modeq_add_right`'s cancellation step); this
/// exposes it as a named theorem, which the prelude had never stated even
/// though it had the proof. Route: `neg t = (-1)*t`, `Int.left_distrib`,
/// `neg_one_mul` twice — no case split on `Int`'s constructors.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_neg_add(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.neg_add, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = d.iadd(a, b);
        let lhs = d.ineg(ab);
        let na = d.ineg(a);
        let nb = d.ineg(b);
        let rhs = d.iadd(na, nb);
        let stmt = d.ieq(lhs, rhs);
        let proof = neg_add(d, a, b);
        (stmt, proof)
    })?;
    Ok(())
}

/// Proves `Eq Int (add (add a b) (add x y)) (add (add a x) (add b y))` — the
/// pure additive rearrangement [`declare_sum_range_add`]'s successor step needs
/// to match the two ways of grouping four summands. A direct transcription of
/// [`super::prod`]'s `mul_swap_inner`: `Int.add_assoc` and `Int.add_comm` have
/// exactly the shapes `Int.mul_assoc`/`Int.mul_comm` do, and — unlike the
/// fuel-row asymmetries that make bitwise transports unsound — **no identity
/// element appears anywhere in this chain**, so nothing about `one` versus
/// `zero` can enter it.
fn add_swap_inner(d: &mut IntDev<'_>, a: ExprId, b: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let p = d.int();
    let ab = d.iadd(a, b);
    let xy = d.iadd(x, y);
    let start = d.iadd(ab, xy);

    // (a+b)+(x+y) = a+(b+(x+y))
    let bxy = d.iadd(b, xy);
    let t1 = d.iadd(a, bxy);
    let p1 = d.const_app(p.add_assoc, &[a, b, xy]);

    // a+(b+(x+y)) = a+((b+x)+y)
    let bx = d.iadd(b, x);
    let bx_y = d.iadd(bx, y);
    let t2 = d.iadd(a, bx_y);
    let assoc_bxy = d.const_app(p.add_assoc, &[b, x, y]); // Eq ((b+x)+y) (b+(x+y))
    let assoc_bxy_rev = d.isymm(bx_y, bxy, assoc_bxy);
    let p2 = d.icongr(bxy, bx_y, assoc_bxy_rev, &|d, t| d.iadd(a, t));

    // a+((b+x)+y) = a+((x+b)+y)
    let xb = d.iadd(x, b);
    let xb_y = d.iadd(xb, y);
    let t3 = d.iadd(a, xb_y);
    let comm_bx = d.const_app(p.add_comm, &[b, x]); // Eq (b+x) (x+b)
    let p3 = d.icongr(bx, xb, comm_bx, &|d, t| {
        let ty_ = d.iadd(t, y);
        d.iadd(a, ty_)
    });

    // a+((x+b)+y) = a+(x+(b+y))
    let by = d.iadd(b, y);
    let x_by = d.iadd(x, by);
    let t4 = d.iadd(a, x_by);
    let assoc_xby = d.const_app(p.add_assoc, &[x, b, y]); // Eq ((x+b)+y) (x+(b+y))
    let p4 = d.icongr(xb_y, x_by, assoc_xby, &|d, t| d.iadd(a, t));

    // a+(x+(b+y)) = (a+x)+(b+y)
    let ax = d.iadd(a, x);
    let end_ = d.iadd(ax, by);
    let assoc_axby = d.const_app(p.add_assoc, &[a, x, by]); // Eq ((a+x)+(b+y)) (a+(x+(b+y)))
    let assoc_axby_rev = d.isymm(end_, t4, assoc_axby);

    let (_e, proof) = d.ichain(
        start,
        &[
            (t1, p1),
            (t2, p2),
            (t3, p3),
            (t4, p4),
            (end_, assoc_axby_rev),
        ],
    );
    proof
}

/// `Int.sumRange_congr :
///   ∀ f g n, (∀ k, Eq Int (f k) (g k)) →
///     Eq Int (sumRange f n) (sumRange g n)`
///
/// Induction on `n`, mirroring [`super::prod::declare_prod_range_congr`]: the
/// base case is `Eq.refl zero` (`sumRange _ zero` computes to `Int.zero`
/// regardless of the function), the successor case rewrites the prior sum by
/// the induction hypothesis and the fresh term by the pointwise hypothesis.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_sum_range_congr(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

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
        let eq = d.ieq(fk, gk);
        d.pi_fv(k_fv, nat, eq)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let lhs = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.const_app(p.sum_range, &[g, x]);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_i = d.izero();
            d.irefl(zero_i)
        },
        &|d, j, ih| {
            let f_prior = d.const_app(p.sum_range, &[f, j]);
            let g_prior = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = d.iadd(f_prior, fj);
            let mid = d.iadd(g_prior, fj);
            let h1 = d.icongr(f_prior, g_prior, ih, &|d, t| d.iadd(t, fj));
            let end = d.iadd(g_prior, gj);
            let pointwise_j = d.apply(h, &[j]);
            let h2 = d.icongr(fj, gj, pointwise_j, &|d, t| d.iadd(g_prior, t));
            let (_, proof) = d.ichain(start, &[(mid, h1), (end, h2)]);
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
    d.declare_theorem(p.sum_range_congr, ty, value)
}

/// `Int.sumRange_add :
///   ∀ f g n, Eq Int (sumRange (fun k => add (f k) (g k)) n)
///     (add (sumRange f n) (sumRange g n))`
/// — a sum of pointwise sums is the sum of the two sums.
///
/// Induction on `n`. The base case is `Int.add_zero zero` read backwards (both
/// sides reduce to `Int.zero`); the successor step rewrites the prior through
/// the induction hypothesis and regroups the four summands
/// `(Sf+Sg)+(f j+g j) = (Sf+f j)+(Sg+g j)` via [`add_swap_inner`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_sum_range_add(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // fg := fun k => add (f k) (g k).
    let fg_lambda = |d: &mut IntDev<'_>| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let body = d.iadd(fk, gk);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let fg = fg_lambda(d);
        let lhs = d.const_app(p.sum_range, &[fg, x]);
        let sf = d.const_app(p.sum_range, &[f, x]);
        let sg = d.const_app(p.sum_range, &[g, x]);
        let rhs = d.iadd(sf, sg);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_i = d.izero();
            let zero_zero = d.iadd(zero_i, zero_i);
            let add_zero_pf = d.const_app(p.add_zero, &[zero_i]); // Eq (zero+zero) zero
            d.isymm(zero_zero, zero_i, add_zero_pf)
        },
        &|d, j, ih| {
            // ih : Eq Int (sumRange fg j) (add (sumRange f j) (sumRange g j))
            let sf_j = d.const_app(p.sum_range, &[f, j]);
            let sg_j = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let fj_gj = d.iadd(fj, gj);

            let sfg_j = {
                let fg = fg_lambda(d);
                d.const_app(p.sum_range, &[fg, j])
            };
            let start = d.iadd(sfg_j, fj_gj);
            let sf_sg = d.iadd(sf_j, sg_j);
            let mid = d.iadd(sf_sg, fj_gj);
            let step1 = d.icongr(sfg_j, sf_sg, ih, &|d, t| d.iadd(t, fj_gj));

            let end_ = add_swap_inner(d, sf_j, sg_j, fj, gj);
            let (_e, proof) = d.ichain(start, &[(mid, step1)]);
            let sf_fj = d.iadd(sf_j, fj);
            let sg_gj = d.iadd(sg_j, gj);
            let final_target = d.iadd(sf_fj, sg_gj);
            d.itrans(start, mid, final_target, proof, end_)
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
    d.declare_theorem(p.sum_range_add, ty, value)
}

/// `Int.sumRange_neg :
///   ∀ f n, Eq Int (sumRange (fun k => neg (f k)) n) (neg (sumRange f n))`
/// — negation pulls out of a finite sum.
///
/// Induction on `n`. The base case is `Eq.refl zero`: `Int.neg Int.zero`
/// δι-reduces (`neg (ofNat 0) → negOfNat 0 → ofNat 0`), so no `neg_zero` lemma
/// is needed and none exists in this prelude. The successor step is
/// [`super::modeq::neg_add`] read backwards.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_sum_range_neg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // nf := fun k => neg (f k).
    let nf_lambda = |d: &mut IntDev<'_>| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let body = d.ineg(fk);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let nf = nf_lambda(d);
        let lhs = d.const_app(p.sum_range, &[nf, x]);
        let sf = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.ineg(sf);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_i = d.izero();
            d.irefl(zero_i)
        },
        &|d, j, ih| {
            // ih : Eq Int (sumRange nf j) (neg (sumRange f j))
            let sf_j = d.const_app(p.sum_range, &[f, j]);
            let fj = d.apply(f, &[j]);
            let n_fj = d.ineg(fj);

            let snf_j = {
                let nf = nf_lambda(d);
                d.const_app(p.sum_range, &[nf, j])
            };
            let start = d.iadd(snf_j, n_fj);
            let neg_sf = d.ineg(sf_j);
            let mid = d.iadd(neg_sf, n_fj);
            let step1 = d.icongr(snf_j, neg_sf, ih, &|d, t| d.iadd(t, n_fj));

            // neg_add(Sf, f j) : Eq (neg (Sf + f j)) ((neg Sf) + (neg (f j)))
            let sum_j = d.iadd(sf_j, fj);
            let end_ = d.ineg(sum_j);
            let distrib = neg_add(d, sf_j, fj);
            let step2 = d.isymm(end_, mid, distrib);

            let (_e, proof) = d.ichain(start, &[(mid, step1), (end_, step2)]);
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
    d.declare_theorem(p.sum_range_neg, ty, value)
}

/// `Int.sumRange_sub :
///   ∀ f g n, Eq Int (sumRange (fun k => sub (f k) (g k)) n)
///     (sub (sumRange f n) (sumRange g n))`
/// — **the lemma Eisenstein's lemma is blocked on**: subtraction inside a
/// finite sum.
///
/// No induction. `Int.sub a b := add a (neg b)` is a plain non-recursive
/// `Definition`, so the stated left-hand side is definitionally
/// `sumRange (fun k => add (f k) ((fun j => neg (g j)) k)) n` — which is
/// [`declare_sum_range_add`] instantiated at `g := fun j => neg (g j)`. One
/// `icongr` through [`declare_sum_range_neg`] finishes it, and the folded
/// `Int.sub` on the right is recovered by the same δ-unfold `sub.rs`'s module
/// doc describes ("state folded, prove unfolded").
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_sum_range_sub(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // ng := fun k => neg (g k); the instance of sumRange_add/sumRange_neg used.
    let ng = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let gk = d.apply(g, &[k]);
        let body = d.ineg(gk);
        d.lam_fv(k_fv, nat, body)
    };

    // Stated LHS: sumRange (fun k => sub (f k) (g k)) n.
    let sub_lambda = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let body = d.isub(fk, gk);
        d.lam_fv(k_fv, nat, body)
    };
    let start = d.const_app(p.sum_range, &[sub_lambda, n]);

    let sf = d.const_app(p.sum_range, &[f, n]);
    let sng = d.const_app(p.sum_range, &[ng, n]);
    let mid = d.iadd(sf, sng);
    // sumRange_add f ng n : Eq (sumRange (fun k => add (f k) (ng k)) n) (Sf + Sng),
    // whose left-hand side is defeq to `start` (β on `ng k`, δ on `Int.sub`).
    let step1 = d.const_app(p.sum_range_add, &[f, ng, n]);

    let sg = d.const_app(p.sum_range, &[g, n]);
    let neg_sg = d.ineg(sg);
    let end_ = d.iadd(sf, neg_sg);
    // sumRange_neg g n : Eq (sumRange ng n) (neg (sumRange g n)).
    let neg_pf = d.const_app(p.sum_range_neg, &[g, n]);
    let step2 = d.icongr(sng, neg_sg, neg_pf, &|d, t| d.iadd(sf, t));

    let (_e, proof) = d.ichain(start, &[(mid, step1), (end_, step2)]);

    // Stated RHS: the folded `Int.sub (sumRange f n) (sumRange g n)`, defeq to
    // `end_`.
    let rhs = d.isub(sf, sg);
    let stmt = d.ieq(start, rhs);

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
    d.declare_theorem(p.sum_range_sub, ty, value)
}

/// `Int.sumRange_ofNat :
///   ∀ (f : Nat → Nat) (n : Nat),
///     Eq Int (sumRange (fun k => ofNat (f k)) n) (ofNat (Nat.sumRange f n))`
/// — the ℕ→ℤ bridge: a finite sum of coerced terms is the coercion of the `Nat`
/// sum.
///
/// This is the lemma that lets a lattice-point *count* — which lives in `Nat`,
/// and which `Nat.countRectangle_partition` produces — enter a signed identity.
/// Both steps are free: `Int.add (ofNat a) (ofNat b) ≡ ofNat (Nat.add a b)`
/// holds at symbolic arguments because `Int.add`'s `ofNat`/`ofNat` minor
/// premise is literally `ofNat (Nat.add m n)`, and `Int.zero ≡ ofNat Nat.zero`
/// by δ. So the induction is `Eq.refl` at the base and a single `icongr` at the
/// step, with the defeq check bridging `add (ofNat _) (ofNat _)` to
/// `ofNat (Nat.add _ _)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_sum_range_of_nat(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let nat_fn_ty = d.arrow(nat, nat);
    let nat_sum_range = d.prelude().sum_range;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // coe := fun k => ofNat (f k).
    let coe_lambda = |d: &mut IntDev<'_>| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let body = d.of_nat(fk);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let coe = coe_lambda(d);
        let lhs = d.const_app(p.sum_range, &[coe, x]);
        let nat_sum = d.const_app(nat_sum_range, &[f, x]);
        let rhs = d.of_nat(nat_sum);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_i = d.izero();
            d.irefl(zero_i)
        },
        &|d, j, ih| {
            // ih : Eq Int (sumRange coe j) (ofNat (Nat.sumRange f j))
            let scoe_j = {
                let coe = coe_lambda(d);
                d.const_app(p.sum_range, &[coe, j])
            };
            let nat_sum_j = d.const_app(nat_sum_range, &[f, j]);
            let coe_sum_j = d.of_nat(nat_sum_j);
            let fj = d.apply(f, &[j]);
            let coe_fj = d.of_nat(fj);
            let start = d.iadd(scoe_j, coe_fj);
            let end_ = d.iadd(coe_sum_j, coe_fj);
            let step = d.icongr(scoe_j, coe_sum_j, ih, &|d, t| d.iadd(t, coe_fj));
            let (_e, proof) = d.ichain(start, &[(end_, step)]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, nat_fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, nat_fn_ty, over_n)
    };
    d.declare_theorem(p.sum_range_of_nat, ty, value)
}

/// `Int.modEq_sumRange :
///   ∀ n f g m, (∀ k, ModEq n (f k) (g k)) →
///     ModEq n (sumRange f m) (sumRange g m)`
/// — the mod-`n` reader: a finite sum reduces modulo `n` term by term. This is
/// the mod-2 bookkeeping step Eisenstein's lemma reads its conclusion through.
///
/// **Unconditional in `n`**, unlike [`super::prod::declare_modeq_prod_range`],
/// which carries `0 < n`. That is not an oversight in either direction: the
/// product's step goes through `Int.ModEq.mul`, whose statement here is
/// positivity-scoped, while the sum's step goes through `Int.ModEq.add_right`
/// and `Int.ModEq.add_left`, both proved UNCONDITIONALLY (see
/// `IntPrelude::mod_eq_add_right`'s own note). Transporting the hypothesis
/// would have forced every consumer to discharge `0 < 2`.
///
/// Induction on `m`: the base case is `ModEq.refl n zero` (both sides compute
/// to `Int.zero`); the step chains `add_right` on the induction hypothesis with
/// `add_left` on the pointwise hypothesis at the predecessor index, exactly the
/// idiom `dvd_gcd_mirrors.rs`'s `modEq_add_right_cancel_general` uses.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_sum_range(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let cong = d.const_app(p.mod_eq, &[n, fk, gk]);
        d.pi_fv(k_fv, nat, cong)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.const_app(p.sum_range, &[g, x]);
        d.const_app(p.mod_eq, &[n, lhs, rhs])
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_i = d.izero();
            d.const_app(p.mod_eq_refl, &[n, zero_i])
        },
        &|d, j, ih| {
            let sf_j = d.const_app(p.sum_range, &[f, j]);
            let sg_j = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);

            // ModEq n (Sf + f j) (Sg + f j)
            let step1 = d.const_app(p.mod_eq_add_right, &[n, sf_j, sg_j, fj, ih]);
            // ModEq n (Sg + f j) (Sg + g j)
            let h_j = d.apply(h, &[j]);
            let step2 = d.const_app(p.mod_eq_add_left, &[n, fj, gj, sg_j, h_j]);

            let sf_fj = d.iadd(sf_j, fj);
            let sg_fj = d.iadd(sg_j, fj);
            let sg_gj = d.iadd(sg_j, gj);
            d.const_app(p.mod_eq_trans, &[n, sf_fj, sg_fj, sg_gj, step1, step2])
        },
        m,
    );

    let ty = {
        let with_h = d.pi_fv(h_fv, pointwise, stmt);
        let over_m = d.pi_fv(m_fv, nat, with_h);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        let over_f = d.pi_fv(f_fv, fn_ty, over_g);
        d.pi_fv(n_fv, int_ty, over_f)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, pointwise, proof);
        let over_m = d.lam_fv(m_fv, nat, with_h);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        let over_f = d.lam_fv(f_fv, fn_ty, over_g);
        d.lam_fv(n_fv, int_ty, over_f)
    };
    d.declare_theorem(p.mod_eq_sum_range, ty, value)
}
