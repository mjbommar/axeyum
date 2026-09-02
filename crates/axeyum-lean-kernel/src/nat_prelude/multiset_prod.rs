//! `Nat.Multiset.prod_add` — the product of a multiset sum, and the three
//! general `Nat.prodRange` laws it needs.
//!
//! # What this closes
//!
//! `docs/plan/status/nat-multiset.md` hands off exactly one blocker for the
//! COMPUTED form of prime factorization: `prod (add m₁ m₂) = prod m₁ * prod m₂`,
//! "a product-regrouping law across three different bounds". The three bounds
//! are the point — `prod` folds over `bound m`, and `Nat.Multiset.add`'s bound
//! is the SUM `bound m₁ + bound m₂`, so the two sides of the equation are folds
//! over `b₁ + b₂`, `b₁` and `b₂` respectively, and no single congruence lemma
//! relates them.
//!
//! The handoff named `Int.prodRange_split` and `Nat.prodRangeIf` as candidates
//! and did not test whether either transports. Neither does, and the reason is
//! worth recording rather than rediscovering:
//!
//! - **`Int.prodRange_split` is the wrong shape.** It splits ONE function's
//!   fold at a point: `prodRange f (a + b) = prodRange f a * prodRange (fun k =>
//!   f (a + k)) b`. The upper half is a *shifted* fold of the same `f`, whereas
//!   what is needed here is the upper half of `f₁` collapsing to `1`. Its Int
//!   proof would transport, but it would leave the shifted fold to be evaluated
//!   afterwards, which is strictly more work than proving the collapse directly.
//! - **`Nat.prodRangeIf` is a selector, not a regrouping law.** Its only
//!   theorems are `_zero`, `_succ` and `_congr_lt`; nothing about it relates a
//!   product over `b₁ + b₂` to one over `b₁`.
//!
//! So all three laws below are new, and none of them mentions `Nat.Multiset`:
//!
//! - `Nat.prodRange_congr : ∀ f g n, (∀ i, f i = g i) → prodRange f n =
//!   prodRange g n` — the Nat twin of `Int.prodRange_congr`. Needed because
//!   this kernel has no `funext`, so a pointwise identity cannot be pushed
//!   under `prodRange` by rewriting the function argument.
//! - `Nat.prodRange_mul : ∀ f g n, prodRange (fun i => f i * g i) n =
//!   prodRange f n * prodRange g n` — the Nat twin of `Int.prodRange_mul`.
//!   Induction on `n`; the successor step is a four-factor rearrangement
//!   `(A·B)·(a·b) = (A·a)·(B·b)` and needs `mul_assoc` three times and
//!   `mul_comm` once.
//! - `Nat.prodRange_add_of_one_above : ∀ f k j, (∀ i, k ≤ i → f i = 1) →
//!   prodRange f (k + j) = prodRange f k` — extending a fold past its support
//!   changes nothing. Induction on `j`, and note the shape: `Nat.add` recurses
//!   on its RIGHT argument, so `add k (succ m)` reduces to `succ (add k m)` for
//!   symbolic `k`, and the induction goes on `j` for exactly that reason. The
//!   `Le k n`-hypothesised form (`prodRange f n = prodRange f k` given `k ≤ n`)
//!   would need `le_dest` to recover the same `j` and buys nothing.
//!
//! # The assembly
//!
//! Write `f₁ q := q ^ count m₁ q`, `f₂ q := q ^ count m₂ q`, `B := b₁ + b₂`.
//!
//! 1. `count (add m₁ m₂) q = count m₁ q + count m₂ q` (`count_add`) and
//!    `q ^ (c₁ + c₂) = q ^ c₁ * q ^ c₂` (`pow_add`) give the pointwise identity
//!    `(fun q => q ^ count (add m₁ m₂) q) q = f₁ q * f₂ q`, which
//!    `prodRange_congr` pushes under the fold. One congruence does both
//!    rewrites, because both are unconditional in `q`.
//! 2. `prodRange_mul` splits the fold into `prodRange f₁ B * prodRange f₂ B`.
//! 3. `prodRange_add_of_one_above` collapses each factor to its own bound:
//!    above `b₁`, `count m₁` is `0` (`count_eq_zero_of_bound_le`, which needs no
//!    well-formedness hypothesis because `count` truncates in its own
//!    definition) and `q ^ 0 = 1` (`pow_zero`). The right factor needs
//!    `add_comm` first, since the lemma extends on the RIGHT and `B` is
//!    `b₁ + b₂`, not `b₂ + b₁`.
//!
//! Every helper hoists each sub-expression into its own `let` before passing it
//! to a `NatOps` method (`&mut NatDev` cannot be reborrowed twice in one call),
//! per this development's house rule.

use super::NatPrelude;
use super::multiset::{ms_bound, ms_count, ms_prod, pow_factor, prod_range};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;
use crate::name::NameId;

/// `∀ binders, stmt`, proved by `proof`. A local copy of `multiset.rs`'s own
/// helper (that one is module-private), per this development's
/// per-file-copy convention.
fn declare_forall(
    d: &mut NatDev<'_>,
    name: NameId,
    binders: &[(u64, ExprId)],
    stmt: ExprId,
    proof: ExprId,
) -> Result<(), KernelError> {
    let mut ty = stmt;
    let mut value = proof;
    for &(fv, binder_ty) in binders.iter().rev() {
        ty = d.pi_fv(fv, binder_ty, ty);
        value = d.lam_fv(fv, binder_ty, value);
    }
    d.declare_theorem(name, ty, value)
}

/// The three general `Nat.prodRange` laws. None mentions `Nat.Multiset`; they
/// are declared here because `Nat.Multiset.prod_add` is their first consumer.
fn declare_prod_range_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    // prodRange_congr : ∀ f g n, (∀ i, Eq (f i) (g i)) →
    //   Eq (prodRange f n) (prodRange g n)
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let hyp_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let fi = d.apply(f, &[i]);
            let gi = d.apply(g, &[i]);
            let body = d.eq(fi, gi);
            d.pi_fv(i_fv, nat, body)
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let claim = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
            let lhs = prod_range(d, &p, f, k);
            let rhs = prod_range(d, &p, g, k);
            d.eq(lhs, rhs)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let one = d.num(1);
            d.refl(one)
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let pf = prod_range(d, &p, f, j);
            let pg = prod_range(d, &p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = d.mul(pf, fj);
            let mid = d.mul(pg, fj);
            let left = d.congr(pf, pg, ih, &|d, y| d.mul(y, fj));
            let hj = d.apply(h, &[j]);
            let right = d.congr(fj, gj, hj, &|d, y| d.mul(pg, y));
            let end = d.mul(pg, gj);
            let (_, proof) = d.chain(start, &[(mid, left), (end, right)]);
            proof
        };
        let proof = d.induct(&claim, &base, &step, n);
        let stmt = claim(d, n);
        declare_forall(
            d,
            p.prod_range_congr,
            &[(f_fv, fn_ty), (g_fv, fn_ty), (n_fv, nat), (h_fv, hyp_ty)],
            stmt,
            proof,
        )?;
    }

    // prodRange_mul : ∀ f g n,
    //   Eq (prodRange (fun i => mul (f i) (g i)) n)
    //      (mul (prodRange f n) (prodRange g n))
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let fi = d.apply(f, &[i]);
            let gi = d.apply(g, &[i]);
            let body = d.mul(fi, gi);
            d.lam_fv(i_fv, nat, body)
        };

        let claim = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
            let lhs = prod_range(d, &p, pointwise, k);
            let pf = prod_range(d, &p, f, k);
            let pg = prod_range(d, &p, g, k);
            let rhs = d.mul(pf, pg);
            d.eq(lhs, rhs)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            // `prodRange _ 0 ≡ 1` on the left and `mul 1 1 ≡ 1` on the right:
            // both sides are closed numerals, so this is `Eq.refl 1`.
            let one = d.num(1);
            d.refl(one)
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            // `X·(a·b)` with `ih : X = A·B`, rearranged to `(A·a)·(B·b)`.
            let x = prod_range(d, &p, pointwise, j);
            let a_big = prod_range(d, &p, f, j);
            let b_big = prod_range(d, &p, g, j);
            let a = d.apply(f, &[j]);
            let b = d.apply(g, &[j]);

            let ab = d.mul(a, b);
            let start = d.mul(x, ab);
            let a_big_b_big = d.mul(a_big, b_big);
            let s1_to = d.mul(a_big_b_big, ab);
            let s1 = d.congr(x, a_big_b_big, ih, &|d, y| d.mul(y, ab));

            // (A·B)·(a·b) = A·(B·(a·b))
            let b_ab = d.mul(b_big, ab);
            let s2_to = d.mul(a_big, b_ab);
            let s2 = d.lemma(p.mul_assoc, &[a_big, b_big, ab]);

            // B·(a·b) = (B·a)·b   [symm of mul_assoc B a b]
            let b_a = d.mul(b_big, a);
            let b_a_b = d.mul(b_a, b);
            let assoc_bab = d.lemma(p.mul_assoc, &[b_big, a, b]);
            let inner3 = d.symm(b_a_b, b_ab, assoc_bab);
            let s3_to = d.mul(a_big, b_a_b);
            let s3 = d.congr(b_ab, b_a_b, inner3, &|d, y| d.mul(a_big, y));

            // (B·a)·b = (a·B)·b
            let a_b = d.mul(a, b_big);
            let comm = d.lemma(p.mul_comm, &[b_big, a]);
            let a_b_b = d.mul(a_b, b);
            let inner4 = d.congr(b_a, a_b, comm, &|d, y| d.mul(y, b));
            let s4_to = d.mul(a_big, a_b_b);
            let s4 = d.congr(b_a_b, a_b_b, inner4, &|d, y| d.mul(a_big, y));

            // (a·B)·b = a·(B·b)
            let b_big_b = d.mul(b_big, b);
            let a_bb = d.mul(a, b_big_b);
            let inner5 = d.lemma(p.mul_assoc, &[a, b_big, b]);
            let s5_to = d.mul(a_big, a_bb);
            let s5 = d.congr(a_b_b, a_bb, inner5, &|d, y| d.mul(a_big, y));

            // A·(a·(B·b)) = (A·a)·(B·b)   [symm of mul_assoc A a (B·b)]
            let a_big_a = d.mul(a_big, a);
            let end = d.mul(a_big_a, b_big_b);
            let assoc_final = d.lemma(p.mul_assoc, &[a_big, a, b_big_b]);
            let s6 = d.symm(end, s5_to, assoc_final);

            let (_, proof) = d.chain(
                start,
                &[
                    (s1_to, s1),
                    (s2_to, s2),
                    (s3_to, s3),
                    (s4_to, s4),
                    (s5_to, s5),
                    (end, s6),
                ],
            );
            proof
        };
        let proof = d.induct(&claim, &base, &step, n);
        let stmt = claim(d, n);
        declare_forall(
            d,
            p.prod_range_mul,
            &[(f_fv, fn_ty), (g_fv, fn_ty), (n_fv, nat)],
            stmt,
            proof,
        )?;
    }

    // prodRange_add_of_one_above : ∀ f k j, (∀ i, Le k i → Eq (f i) 1) →
    //   Eq (prodRange f (add k j)) (prodRange f k)
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let hyp_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.le(k, i);
            let fi = d.apply(f, &[i]);
            let one = d.num(1);
            let concl = d.eq(fi, one);
            let body = d.arrow(bound, concl);
            d.pi_fv(i_fv, nat, body)
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let claim = |d: &mut NatDev<'_>, t: ExprId| -> ExprId {
            let extended = d.add(k, t);
            let lhs = prod_range(d, &p, f, extended);
            let rhs = prod_range(d, &p, f, k);
            d.eq(lhs, rhs)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            // `add k zero ≡ k` — `Nat.add` recurses on its RIGHT argument.
            let at_k = prod_range(d, &p, f, k);
            d.refl(at_k)
        };
        let step = |d: &mut NatDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
            let extended = d.add(k, m);
            let below = prod_range(d, &p, f, extended);
            let at_k = prod_range(d, &p, f, k);
            let tail = d.apply(f, &[extended]);
            let start = d.mul(below, tail);
            let mid = d.mul(at_k, tail);
            let s1 = d.congr(below, at_k, ih, &|d, y| d.mul(y, tail));
            let le = d.lemma(p.le_add_right, &[k, m]);
            let tail_one = d.apply(h, &[extended, le]);
            let one = d.num(1);
            let mid2 = d.mul(at_k, one);
            let s2 = d.congr(tail, one, tail_one, &|d, y| d.mul(at_k, y));
            let s3 = d.lemma(p.mul_one, &[at_k]);
            let (_, proof) = d.chain(start, &[(mid, s1), (mid2, s2), (at_k, s3)]);
            proof
        };
        let proof = d.induct(&claim, &base, &step, j);
        let stmt = claim(d, j);
        declare_forall(
            d,
            p.prod_range_add_of_one_above,
            &[(f_fv, fn_ty), (k_fv, nat), (j_fv, nat), (h_fv, hyp_ty)],
            stmt,
            proof,
        )?;
    }

    Ok(())
}

/// `∀ i, Le (bound m) i → Eq (pow i (count m i)) 1` — above its own bound a
/// multiset's factor function is constantly `1`. `count_eq_zero_of_bound_le`
/// needs no well-formedness hypothesis (`count` truncates in its own
/// definition), so this holds for EVERY multiset.
fn one_above_bound(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let b = ms_bound(d, p, m);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp_ty = d.le(b, i);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let c = ms_count(d, p, m, i);
    let zero = d.zero();
    let vanishes = d.lemma(p.multiset_count_eq_zero_of_bound_le, &[m, i, h]);
    let lifted = d.congr(c, zero, vanishes, &|d, y| d.pow(i, y));
    let from = d.pow(i, c);
    let via = d.pow(i, zero);
    let one = d.num(1);
    let to_one = d.lemma(p.pow_zero, &[i]);
    let body = d.trans(from, via, one, lifted, to_one);
    let with_h = d.lam_fv(h_fv, hyp_ty, body);
    d.lam_fv(i_fv, nat, with_h)
}

/// `Nat.Multiset.prod_add : ∀ m₁ m₂, Eq (prod (add m₁ m₂))
/// (mul (prod m₁) (prod m₂))`. See the module doc for the assembly.
fn declare_prod_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let ms = d.kernel().const_(p.multiset, vec![]);

    let m1_fv = d.fresh_fvar();
    let m1 = d.kernel().fvar(m1_fv);
    let m2_fv = d.fresh_fvar();
    let m2 = d.kernel().fvar(m2_fv);

    let joined = d.const_app(p.multiset_add, &[m1, m2]);
    let b1 = ms_bound(d, &p, m1);
    let b2 = ms_bound(d, &p, m2);
    let big_bound = d.add(b1, b2);

    let count_joined = d.const_app(p.multiset_count, &[joined]);
    let count_1 = d.const_app(p.multiset_count, &[m1]);
    let count_2 = d.const_app(p.multiset_count, &[m2]);
    let factors_joined = pow_factor(d, count_joined);
    let f1 = pow_factor(d, count_1);
    let f2 = pow_factor(d, count_2);

    // `fun q => (q ^ count m1 q) * (q ^ count m2 q)`, written beta-reduced so
    // the chain's intermediate terms stay readable; it is defeq to
    // `prodRange_mul`'s stated `fun i => mul (f1 i) (f2 i)`.
    let split_factors = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let c1 = ms_count(d, &p, m1, q);
        let c2 = ms_count(d, &p, m2, q);
        let left = d.pow(q, c1);
        let right = d.pow(q, c2);
        let body = d.mul(left, right);
        d.lam_fv(q_fv, nat, body)
    };

    // Step 1: the pointwise identity, `count_add` then `pow_add`.
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let cj = ms_count(d, &p, joined, i);
        let c1 = ms_count(d, &p, m1, i);
        let c2 = ms_count(d, &p, m2, i);
        let sum = d.add(c1, c2);
        let hc = d.lemma(p.multiset_count_add, &[m1, m2, i]);
        let lifted = d.congr(cj, sum, hc, &|d, y| d.pow(i, y));
        let split = d.lemma(p.pow_add, &[i, c1, c2]);
        let from = d.pow(i, cj);
        let via = d.pow(i, sum);
        let left = d.pow(i, c1);
        let right = d.pow(i, c2);
        let to = d.mul(left, right);
        let body = d.trans(from, via, to, lifted, split);
        d.lam_fv(i_fv, nat, body)
    };
    let start = prod_range(d, &p, factors_joined, big_bound);
    let after_congr = prod_range(d, &p, split_factors, big_bound);
    let s1 = d.lemma(
        p.prod_range_congr,
        &[factors_joined, split_factors, big_bound, pointwise],
    );

    // Step 2: split the fold.
    let p1_big = prod_range(d, &p, f1, big_bound);
    let p2_big = prod_range(d, &p, f2, big_bound);
    let after_split = d.mul(p1_big, p2_big);
    let s2 = d.lemma(p.prod_range_mul, &[f1, f2, big_bound]);

    // Step 3: collapse the left factor to `b1`.
    let one_above_1 = one_above_bound(d, &p, m1);
    let p1_small = prod_range(d, &p, f1, b1);
    let s3_inner = d.lemma(p.prod_range_add_of_one_above, &[f1, b1, b2, one_above_1]);
    let after_left = d.mul(p1_small, p2_big);
    let s3 = d.congr(p1_big, p1_small, s3_inner, &|d, y| d.mul(y, p2_big));

    // Step 4: `add_comm` and then collapse the right factor to `b2`.
    let one_above_2 = one_above_bound(d, &p, m2);
    let flipped_bound = d.add(b2, b1);
    let comm = d.lemma(p.add_comm, &[b1, b2]);
    let p2_flipped = prod_range(d, &p, f2, flipped_bound);
    let to_flipped = d.congr(big_bound, flipped_bound, comm, &|d, y| {
        prod_range(d, &p, f2, y)
    });
    let p2_small = prod_range(d, &p, f2, b2);
    let flipped_collapse = d.lemma(p.prod_range_add_of_one_above, &[f2, b2, b1, one_above_2]);
    let s4_inner = d.trans(p2_big, p2_flipped, p2_small, to_flipped, flipped_collapse);
    let end = d.mul(p1_small, p2_small);
    let s4 = d.congr(p2_big, p2_small, s4_inner, &|d, y| d.mul(p1_small, y));

    let (_, proof) = d.chain(
        start,
        &[
            (after_congr, s1),
            (after_split, s2),
            (after_left, s3),
            (end, s4),
        ],
    );

    let lhs = ms_prod(d, &p, joined);
    let r1 = ms_prod(d, &p, m1);
    let r2 = ms_prod(d, &p, m2);
    let rhs = d.mul(r1, r2);
    let stmt = d.eq(lhs, rhs);
    declare_forall(
        d,
        p.multiset_prod_add,
        &[(m1_fv, ms), (m2_fv, ms)],
        stmt,
        proof,
    )
}

/// The three `Nat.prodRange` laws and `Nat.Multiset.prod_add`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_multiset_prod_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_prod_range_laws(d, p)?;
    declare_prod_add(d, p)?;
    Ok(())
}
