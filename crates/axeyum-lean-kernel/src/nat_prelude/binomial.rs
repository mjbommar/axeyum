//! The binomial theorem over ℕ, `Nat.add_pow`.
//!
//! [`super::choose`] gives us `Nat.choose` and Pascal's rule
//! (`choose_succ_succ`, closing by `refl` alone for generic `n,k`). This
//! module builds the finite-sum reindexing toolkit the induction needs beyond
//! what [`super::algebra`] already has — [`sum_range_add`](declare_sum_range_add),
//! a FRONT-peeling counterpart to the defining (back-peeling) `sum_range_succ`
//! ([`sum_range_shift_front`](declare_sum_range_shift_front)), and a bounded
//! pointwise congruence ([`sum_range_congr_lt`](declare_sum_range_congr_lt))
//! — checks the theorem's STATEMENT shape at `n=0` and `n=1`
//! ([`declare_add_pow_sanity`]) before attempting the general induction, and
//! then proves it ([`declare_add_pow`]).
//!
//! # The induction step, staged
//!
//! The classical step splits `(a+b)^(n+1) = (a+b)*S(n)` (`S(n)` the sum-form
//! of `(a+b)^n`) into `a*S(n) + b*S(n)`, then matches each piece against a
//! front-peel of `S(n+1)`'s OWN sum, using Pascal's rule to combine the
//! peeled tail. This module builds that assembly in four stages:
//!
//! 1. **Reassociation helpers** ([`mul_left_comm`], [`add_left_comm`]) — the
//!    two three-term rearrangements every per-term identity below needs, so
//!    no use site reconstructs `mul_assoc`+`mul_comm` (resp.
//!    `add_assoc`+`add_comm`) by hand.
//! 2. **The `a`-side** ([`pascal_split_term`], [`a_side_lemma`]) —
//!    unconditional (an `a`-exponent bump via `pow_succ` needs no side
//!    condition), closing with `sum_range_congr` plus `mul_sum_range`.
//! 3. **The `b`-side** ([`u_tail_boundary`], [`b_side_term`],
//!    [`b_side_lemma`]) — needs `succ (n - succ k) = n - k`, only true for
//!    `k < n` ([`super::choose::sub_succ_of_lt`], built for `choose_symm`'s
//!    own case split), applied under `sum_range_congr_lt` (bounded by `n`,
//!    where every index satisfies `k < n` uniformly), plus the tail sum's own
//!    boundary term vanishing (`choose_succ_self_eq_zero`).
//! 4. **Assembly** ([`add_pow_step`], [`declare_add_pow`]) — wires `a*S(n)`,
//!    `b*S(n)`, and the front-peeled, boundary-adjusted (`choose_zero_right`
//!    via [`binom_term_zero_eq_pow_b`]) pieces of `S(n+1)` into one proof
//!    term, closing with [`add_left_comm`] to match the two decompositions up.

use super::NatPrelude;
use super::choose::sub_succ_of_lt;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `fun k => f (succ k)`, the index-shifted function used by
/// [`sum_range_shift_front`](declare_sum_range_shift_front).
fn shifted_fn(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sk = d.succ(k);
    let body = d.apply(f, &[sk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `(a+b)+(c+d) = (a+c)+(b+d)`, returned as a `(target, proof)` chain step
/// (the proof's source is `add(add(a,b),add(c,d))`).
/// `(a+b)+(c+d) = (a+c)+(b+d)`, returned as `(target, proof)`.
///
/// Retired to `crate::ring::nat` (docs/plan/status/460-ring-tactic-1.md): a
/// pure ring-rearrangement chain, now searched for and emitted rather than
/// hand-assembled — one of eight verbatim-duplicated hand proofs of this
/// exact identity across `nat_prelude` (`div_mod_lemmas.rs`, `finite_set.rs`,
/// `fibonacci.rs`, `subset_sum.rs`, `rec_agreement.rs`,
/// `count_range_reversal.rs`, `eisenstein_lemma.rs`).
fn add_add_add_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> (ExprId, ExprId) {
    let ac = d.add(a, c);
    let bd = d.add(b, dd);
    let target = d.add(ac, bd);
    // Generic-then-apply (`prove_eq_at`), not `prove_eq` on the literal
    // arguments: at some call sites `a`/`b`/`c`/`dd` are themselves
    // `div`/`mod` expressions, which `prove_eq` would (correctly) decline
    // `NonRing` on.
    let proof = crate::ring::nat::prove_eq_at(d, p, &[a, b, c, dd], &|d, v| {
        let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
        let ab = d.add(a, b);
        let cd = d.add(c, dd);
        let lhs = d.add(ab, cd);
        let ac = d.add(a, c);
        let bd = d.add(b, dd);
        let rhs = d.add(ac, bd);
        (lhs, rhs)
    })
    .unwrap_or_else(|e| panic!("ring declined add_add_add_comm: {e:?}"));
    (target, proof)
}

/// `sumRange_add : ∀ f g n, sumRange (fun i => f i + g i) n = sumRange f n + sumRange g n`.
///
/// Proved by induction on `n`; the successor case needs the four-term
/// rearrangement `(A+B)+(C+D) = (A+C)+(B+D)` ([`add_add_add_comm`]), since the
/// induction hypothesis rewrites the *inner* pair while `sum_range_succ`
/// produces the *outer* one.
fn declare_sum_range_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let combined_fn = |d: &mut NatDev<'_>, f: ExprId, g: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body = d.add(fi, gi);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let combined = combined_fn(d, f, g);
        let lhs = d.sum_range(combined, x);
        let sf = d.sum_range(f, x);
        let sg = d.sum_range(g, x);
        let rhs = d.add(sf, sg);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &|d, j, ih| {
            let combined = combined_fn(d, f, g);
            let combined_j = d.apply(combined, &[j]);
            let prior_combined = d.sum_range(combined, j);
            let start = d.add(prior_combined, combined_j);

            let sf_j = d.sum_range(f, j);
            let sg_j = d.sum_range(g, j);
            let sfg = d.add(sf_j, sg_j);
            let h1 = d.congr(prior_combined, sfg, ih, &|d, t| d.add(t, combined_j));
            let after_ih = d.add(sfg, combined_j);

            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let fg_j = d.add(fj, gj);
            let h_bridge = d.refl(fg_j); // combined_j ≡ fg_j by beta
            let after_bridge = d.add(sfg, fg_j);
            let h2 = d.congr(combined_j, fg_j, h_bridge, &|d, t| d.add(sfg, t));

            let end = add_add_add_comm(d, &p, sf_j, sg_j, fj, gj);
            let (_e, proof) = d.chain(start, &[(after_ih, h1), (after_bridge, h2), end]);
            proof
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

/// `sumRange_shiftFront : ∀ f n, sumRange f (succ n) = f 0 + sumRange (fun k => f (succ k)) n`
/// — peeling the FRONT term off a finite sum. `sum_range_succ` (the defining
/// equation) already peels the BACK term for free; this direction needs
/// induction, because the front term stays fixed while the bound moves.
fn declare_sum_range_shift_front(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let lhs = d.sum_range(f, sx);
        let zero = d.zero();
        let f0 = d.apply(f, &[zero]);
        let shifted = shifted_fn(d, f);
        let sr = d.sum_range(shifted, x);
        let rhs = d.add(f0, sr);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let f0 = d.apply(f, &[zero]);
            d.lemma(p.zero_add, &[f0])
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let f_prior_succ = d.sum_range(f, sj);
            let f_sj = d.apply(f, &[sj]);
            let start = d.add(f_prior_succ, f_sj);

            let zero = d.zero();
            let f0 = d.apply(f, &[zero]);
            let shifted = shifted_fn(d, f);
            let shifted_j = d.sum_range(shifted, j);
            let mid1 = d.add(f0, shifted_j);
            let h1 = d.congr(f_prior_succ, mid1, ih, &|d, t| d.add(t, f_sj));
            let after_ih = d.add(mid1, f_sj);

            let inner = d.add(shifted_j, f_sj);
            let end = d.add(f0, inner);
            let h2 = d.lemma(p.add_assoc, &[f0, shifted_j, f_sj]);

            let (_e, proof) = d.chain(start, &[(after_ih, h1), (end, h2)]);
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
    d.declare_theorem(p.sum_range_shift_front, ty, value)
}

/// `fun i => Lt i bound -> Eq (f i) (g i)`.
fn bounded_pointwise(d: &mut NatDev<'_>, f: ExprId, g: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let eqn = d.eq(fi, gi);
    let body = d.arrow(hyp, eqn);
    d.pi_fv(i_fv, nat, body)
}

/// `sumRange_congr_lt : ∀ f g n, (∀ i, Lt i n → f i = g i) → sumRange f n = sumRange g n`
/// — [`super::algebra::declare_finite_sum_theorems`]'s `sum_range_congr` with
/// the hypothesis weakened to indices below the bound, which is what a sum
/// with only-conditionally-true summand identities (e.g. involving truncated
/// subtraction) can actually supply.
fn declare_sum_range_congr_lt(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_pointwise(d, f, g, x);
        let lhs = d.sum_range(f, x);
        let rhs = d.sum_range(g, x);
        let eqn = d.eq(lhs, rhs);
        d.arrow(hyp, eqn)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = bounded_pointwise(d, f, g, zero);
            let h_fv = d.fresh_fvar();
            let body = d.refl(zero);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_pointwise(d, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // h_lt_j : ∀ i, Lt i j → f i = g i, weakened from `h` via `i<j → i<succ j`.
            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_j = d.lemma(p.le_succ, &[j]);
                let lifted = d.lemma(p.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let lt_j_sj = d.lemma(p.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = d.sum_range(f, j);
            let g_prior = d.sum_range(g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = d.add(f_prior, fj);
            let mid = d.add(g_prior, fj);
            let h1 = d.congr(f_prior, g_prior, sub1, &|d, t| d.add(t, fj));
            let end = d.add(g_prior, gj);
            let h2 = d.congr(fj, gj, sub2, &|d, t| d.add(g_prior, t));
            let (_e, body) = d.chain(start, &[(mid, h1), (end, h2)]);

            d.lam_fv(h_fv, hyp_ty, body)
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
    d.declare_theorem(p.sum_range_congr_lt, ty, value)
}

/// `fun k => (choose row k * a^k) * b^(row-k)` — the summand of the binomial
/// expansion at `row`, at a POINT (not the lambda; see [`binom_term_fn`]).
pub(super) fn binom_term(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    row: ExprId,
    k: ExprId,
) -> ExprId {
    let c = d.choose(row, k);
    let ak = d.pow(a, k);
    let c_ak = d.mul(c, ak);
    let sub_rk = d.sub(row, k);
    let b_pow = d.pow(b, sub_rk);
    d.mul(c_ak, b_pow)
}

/// `fun k => choose row k * a^k * b^(row-k)`, as a lambda.
pub(super) fn binom_term_fn(d: &mut NatDev<'_>, a: ExprId, b: ExprId, row: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = binom_term(d, a, b, row, k);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `sumRange (fun k => choose row k * a^k * b^(row-k)) (succ row)` — the
/// sum-form of `(a+b)^row`.
pub(super) fn binom_sum(d: &mut NatDev<'_>, a: ExprId, b: ExprId, row: ExprId) -> ExprId {
    let t = binom_term_fn(d, a, b, row);
    let srow = d.succ(row);
    d.sum_range(t, srow)
}

// ============================================================================
// Stage 1: reassociation helpers. Reusable regardless of the binomial theorem
// specifically — every per-term identity below needs exactly one of these two
// three-term rearrangements, and each is named so no use site reconstructs
// `mul_assoc`/`mul_comm` (resp. `add_assoc`/`add_comm`) by hand.
// ============================================================================

/// `mul_left_comm : x*(y*z) = y*(x*z)` — swap the first two factors of a
/// three-factor product, third fixed. Proved the same way `add_right_comm`
/// (`algebra.rs`) proves its additive shape: assoc, comm-on-the-pair, assoc.
///
/// `pub(super)` (rather than the file-private `fn` every other helper in this
/// stage is) so `desc_factorial.rs`/`asc_factorial.rs`'s falling/rising
/// factorial ↔ `choose` bridges can reuse it instead of rebuilding a third
/// copy — see `docs/plan/status/197` on why a private `fn` duplicated across
/// files is a standing hazard here.
pub(super) fn mul_left_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> ExprId {
    let p = *p;
    let yz = d.mul(y, z);
    let start = d.mul(x, yz);
    let xy = d.mul(x, y);
    let xy_z = d.mul(xy, z);
    let h_assoc1 = d.lemma(p.mul_assoc, &[x, y, z]); // xy_z = start
    let h1 = d.symm(xy_z, start, h_assoc1); // start = xy_z
    let yx = d.mul(y, x);
    let yx_z = d.mul(yx, z);
    let h_comm = d.lemma(p.mul_comm, &[x, y]); // xy = yx
    let h2 = d.congr(xy, yx, h_comm, &|d, t| d.mul(t, z)); // xy_z = yx_z
    let xz = d.mul(x, z);
    let target = d.mul(y, xz);
    let h3 = d.lemma(p.mul_assoc, &[y, x, z]); // yx_z = target
    let (_e, proof) = d.chain(start, &[(xy_z, h1), (yx_z, h2), (target, h3)]);
    proof
}

/// `add_left_comm : x+(y+z) = y+(x+z)` — the additive counterpart of
/// [`mul_left_comm`], used to rearrange the three summands
/// `b^(succ n)`, `a*S(n)`, `sumRange U n` in the final assembly.
fn add_left_comm(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, y: ExprId, z: ExprId) -> ExprId {
    let p = *p;
    let yz = d.add(y, z);
    let start = d.add(x, yz);
    let xy = d.add(x, y);
    let xy_z = d.add(xy, z);
    let h_assoc1 = d.lemma(p.add_assoc, &[x, y, z]); // xy_z = start
    let h1 = d.symm(xy_z, start, h_assoc1); // start = xy_z
    let yx = d.add(y, x);
    let yx_z = d.add(yx, z);
    let h_comm = d.lemma(p.add_comm, &[x, y]); // xy = yx
    let h2 = d.congr(xy, yx, h_comm, &|d, t| d.add(t, z)); // xy_z = yx_z
    let xz = d.add(x, z);
    let target = d.add(y, xz);
    let h3 = d.lemma(p.add_assoc, &[y, x, z]); // yx_z = target
    let (_e, proof) = d.chain(start, &[(xy_z, h1), (yx_z, h2), (target, h3)]);
    proof
}

// ============================================================================
// Shared term builders for the induction step.
// ============================================================================

/// `(choose n (succ k) * a^(succ k)) * b^(n-k)` — the second summand of
/// Pascal's split of `binom_term a b (succ n) (succ k)` (see
/// [`pascal_split_term`]), once `succ_sub_succ` has already moved its
/// `b`-exponent from `sub (succ n) (succ k)` to `sub n k`.
fn pascal_tail_term(d: &mut NatDev<'_>, a: ExprId, b: ExprId, n: ExprId, k: ExprId) -> ExprId {
    let sk = d.succ(k);
    let c = d.choose(n, sk);
    let ak = d.pow(a, sk);
    let c_ak = d.mul(c, ak);
    let sub_nk = d.sub(n, k);
    let b_pow = d.pow(b, sub_nk);
    d.mul(c_ak, b_pow)
}

/// `fun k => pascal_tail_term a b n k`, as a lambda (built directly, not via
/// `apply`, so it matches the reduced shape [`pascal_split_term`] proves
/// pointwise identities against).
fn pascal_tail_fn(d: &mut NatDev<'_>, a: ExprId, b: ExprId, n: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = pascal_tail_term(d, a, b, n, k);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => a * binom_term a b n k`, as a lambda (built directly).
fn a_scaled_binom_term_fn(d: &mut NatDev<'_>, a: ExprId, b: ExprId, n: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let term = binom_term(d, a, b, n, k);
    let body = d.mul(a, term);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `binom_term a b row 0 = pow b row` — the front boundary term of any row's
/// expansion, needed at `row = n` (the `b`-side) and `row = succ n` (the final
/// front-peel of `S(succ n)`), hence generalized over `row` rather than
/// specialized to either use site.
pub(super) fn binom_term_zero_eq_pow_b(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    row: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let start = binom_term(d, a, b, row, zero);

    // `start` is definitionally `mul(mul(choose(row,0), 1), pow(b,row))`:
    // `pow(a,0)` reduces to `1` (`pow_zero`, an ι-step) and `sub(row,0)`
    // reduces to `row` (`sub_zero`, likewise), both pure computation.
    let c0 = d.choose(row, zero);
    let one = d.num(1);
    let c0_one = d.mul(c0, one);
    let bpow_row = d.pow(b, row);
    let mid0 = d.mul(c0_one, bpow_row);
    let h_defeq = d.refl(mid0); // Eq(start, mid0) via the two ι-reductions above

    // choose row 0 = 1 (a genuine theorem, not definitional).
    let h_c0 = d.lemma(p.choose_zero_right, &[row]);
    let one_one = d.mul(one, one);
    let mid1 = d.mul(one_one, bpow_row);
    let h1 = d.congr(c0, one, h_c0, &|d, t| {
        let t_one = d.mul(t, one);
        d.mul(t_one, bpow_row)
    });

    // 1 * 1 = 1.
    let h_oo = d.lemma(p.one_mul, &[one]);
    let mid2 = d.mul(one, bpow_row);
    let h2 = d.congr(one_one, one, h_oo, &|d, t| d.mul(t, bpow_row));

    // 1 * pow(b,row) = pow(b,row).
    let h3 = d.lemma(p.one_mul, &[bpow_row]);

    let (_e, proof) = d.chain(
        start,
        &[(mid0, h_defeq), (mid1, h1), (mid2, h2), (bpow_row, h3)],
    );
    proof
}

// ============================================================================
// Stage 2: the a-side of the induction step.
// ============================================================================

/// `binom_term a b (succ n) (succ k) = a * binom_term a b n k + pascal_tail_term a b n k`,
/// for ALL `k` — unconditional, since the only side fact used besides Pascal's
/// rule (itself definitional) is `succ_sub_succ`, which holds for every `n,k`.
/// This is the per-term content the `a`-side of the induction step reindexes
/// through (via `sum_range_congr`, since it needs no bound on `k`).
fn pascal_split_term(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    k: ExprId,
) -> ExprId {
    let p = *p;
    let sn = d.succ(n);
    let sk = d.succ(k);

    let lhs = binom_term(d, a, b, sn, sk);

    let c_sn_sk = d.choose(sn, sk);
    let ak = d.pow(a, sk);
    let sub_sn_sk = d.sub(sn, sk);
    let bpow_sn_sk = d.pow(b, sub_sn_sk);

    // Step 1: Pascal's rule expands the leading `choose (succ n) (succ k)`.
    let c1 = d.choose(n, k);
    let c2 = d.choose(n, sk);
    let c1_c2 = d.add(c1, c2);
    let h_pascal = d.lemma(p.choose_succ_succ, &[n, k]); // c_sn_sk = c1_c2
    let inner1 = d.mul(c1_c2, ak);
    let stage1 = d.mul(inner1, bpow_sn_sk);
    let h1 = d.congr(c_sn_sk, c1_c2, h_pascal, &|d, t| {
        let inner = d.mul(t, ak);
        d.mul(inner, bpow_sn_sk)
    });

    // Step 2: right_distrib splits the inner product over the Pascal sum.
    let p_ak = d.mul(c1, ak);
    let q_ak = d.mul(c2, ak);
    let p_q = d.add(p_ak, q_ak);
    let stage2 = d.mul(p_q, bpow_sn_sk);
    let h_rd1 = d.lemma(p.right_distrib, &[c1, c2, ak]); // inner1 = p_q
    let h2 = d.congr(inner1, p_q, h_rd1, &|d, t| d.mul(t, bpow_sn_sk));

    // Step 3: right_distrib splits the outer product over the two terms.
    let p_bp = d.mul(p_ak, bpow_sn_sk);
    let q_bp = d.mul(q_ak, bpow_sn_sk);
    let stage3 = d.add(p_bp, q_bp);
    let h3 = d.lemma(p.right_distrib, &[p_ak, q_ak, bpow_sn_sk]); // stage2 = stage3

    // Step 4: succ_sub_succ moves the b-exponent from `sub(succ n,succ k)` to
    // `sub n k`, inside both summands at once.
    let sub_nk = d.sub(n, k);
    let bpow_nk = d.pow(b, sub_nk);
    let p_bpd = d.mul(p_ak, bpow_nk);
    let q_bpd = d.mul(q_ak, bpow_nk);
    let stage4 = d.add(p_bpd, q_bpd);
    let h_sub = d.lemma(p.succ_sub_succ, &[n, k]); // sub_sn_sk = sub_nk
    let h_sub_pow = d.congr(sub_sn_sk, sub_nk, h_sub, &|d, x| d.pow(b, x)); // bpow_sn_sk = bpow_nk
    let h4 = d.congr(bpow_sn_sk, bpow_nk, h_sub_pow, &|d, x| {
        let mp = d.mul(p_ak, x);
        let mq = d.mul(q_ak, x);
        d.add(mp, mq)
    });

    // Steps 5-7: rewrite `p_bpd = mul(mul(c1,ak), bpow_nk)` (ak the BUMPED
    // exponent) into `a * binom_term a b n k`, via the `pow_succ` unfold of
    // `ak` and two reassociations (`mul_assoc` then `mul_left_comm`).
    let term_nk = binom_term(d, a, b, n, k);
    let a_term_nk = d.mul(a, term_nk);

    let ak0 = d.pow(a, k);
    let ak0_a = d.mul(ak0, a);
    let h_pow_succ = d.lemma(p.pow_succ, &[a, k]); // ak = ak0_a
    let c1_ak0a = d.mul(c1, ak0_a);
    let stage5 = d.mul(c1_ak0a, bpow_nk);
    let h5 = d.congr(ak, ak0_a, h_pow_succ, &|d, x| {
        let cx = d.mul(c1, x);
        d.mul(cx, bpow_nk)
    });

    let x_factor = d.mul(c1, ak0); // term_nk's own leading factor
    let x_a = d.mul(x_factor, a);
    let stage6 = d.mul(x_a, bpow_nk);
    let h_assoc_pull = d.lemma(p.mul_assoc, &[c1, ak0, a]); // x_a = c1_ak0a
    let h6_base = d.symm(x_a, c1_ak0a, h_assoc_pull); // c1_ak0a = x_a
    let h6 = d.congr(c1_ak0a, x_a, h6_base, &|d, t| d.mul(t, bpow_nk));

    let a_bpow_nk = d.mul(a, bpow_nk);
    let stage7 = d.mul(x_factor, a_bpow_nk);
    let h7 = d.lemma(p.mul_assoc, &[x_factor, a, bpow_nk]); // stage6 = stage7

    // `mul_left_comm` gives Eq(stage7, mul(a, mul(x_factor,bpow_nk))); the
    // second argument is `term_nk` up to construction (`x_factor = mul(c1,ak0)`
    // matches `binom_term`'s own leading factor exactly), so its type is
    // accepted here up to definitional equality against `a_term_nk`.
    let h8 = mul_left_comm(d, &p, x_factor, a, bpow_nk); // stage7 = a_term_nk

    let (_e_left, left_chain) = d.chain(
        p_bpd,
        &[(stage5, h5), (stage6, h6), (stage7, h7), (a_term_nk, h8)],
    );

    // Combine: rewrite stage4's LEFT summand via `left_chain`, then rewrite
    // the RIGHT summand `q_bpd` into `pascal_tail_term` (an identical
    // construction, so the bridge is `refl`).
    let tail = pascal_tail_term(d, a, b, n, k);
    let stage4b = d.add(a_term_nk, q_bpd);
    let h_left = d.congr(p_bpd, a_term_nk, left_chain, &|d, t| d.add(t, q_bpd));
    let final_target = d.add(a_term_nk, tail);
    let h_tail = d.refl(tail);
    let h_right = d.congr(q_bpd, tail, h_tail, &|d, t| d.add(a_term_nk, t));

    let (_e, proof) = d.chain(
        lhs,
        &[
            (stage1, h1),
            (stage2, h2),
            (stage3, h3),
            (stage4, h4),
            (stage4b, h_left),
            (final_target, h_right),
        ],
    );
    proof
}

/// The `a`-side of the induction step: reindex the front-peeled TAIL of
/// `S(succ n)`'s own sum (`fun k => binom_term a b (succ n) (succ k)`) through
/// [`pascal_split_term`] via `sum_range_congr` (unconditional — no bound on
/// `k` needed), then split the resulting sum via `sum_range_add` and collapse
/// its first half via `mul_sum_range`.
///
/// Proves `sumRange (fun k => binom_term a b (succ n) (succ k)) (succ n)
///        = a * S(n) + sumRange (pascal_tail_term a b n) (succ n)`.
fn a_side_lemma(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let sn = d.succ(n);
    let term_sn_fn = binom_term_fn(d, a, b, sn);
    let f = shifted_fn(d, term_sn_fn);

    let g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let term_nk = binom_term(d, a, b, n, k);
        let a_term = d.mul(a, term_nk);
        let tail = pascal_tail_term(d, a, b, n, k);
        let body = d.add(a_term, tail);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, body)
    };

    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = pascal_split_term(d, &p, a, b, n, i);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };
    let h_congr = d.lemma(p.sum_range_congr, &[f, g, sn, pointwise]);
    // h_congr : Eq(sumRange f sn, sumRange g sn)

    let f1 = a_scaled_binom_term_fn(d, a, b, n);
    let g1 = pascal_tail_fn(d, a, b, n);
    let h_sra = d.lemma(p.sum_range_add, &[f1, g1, sn]);
    // h_sra : Eq(sumRange g sn, add(sumRange f1 sn, sumRange g1 sn)) up to the
    // definitional match between `g` and `sum_range_add`'s own combined `f+g`.

    let term_n_fn = binom_term_fn(d, a, b, n);
    let s_n = d.sum_range(term_n_fn, sn);
    let h_msr = d.lemma(p.mul_sum_range, &[a, term_n_fn, sn]);
    // h_msr : Eq(mul(a,s_n), sumRange f1 sn) up to the definitional match
    // between `f1` and `mul_sum_range`'s own scaled function.
    let mul_a_sn = d.mul(a, s_n);
    let sum_f1_sn = d.sum_range(f1, sn);
    let h_msr_symm = d.symm(mul_a_sn, sum_f1_sn, h_msr);

    let sum_g1_sn = d.sum_range(g1, sn);
    let rhs_sra = d.add(sum_f1_sn, sum_g1_sn);
    let final_target = d.add(mul_a_sn, sum_g1_sn);
    let h_final = d.congr(sum_f1_sn, mul_a_sn, h_msr_symm, &|d, t| d.add(t, sum_g1_sn));

    let sum_f_sn = d.sum_range(f, sn);
    let sum_g_sn = d.sum_range(g, sn);
    let (_e, proof) = d.chain(
        sum_f_sn,
        &[
            (sum_g_sn, h_congr),
            (rhs_sra, h_sra),
            (final_target, h_final),
        ],
    );
    proof
}

// ============================================================================
// Stage 3: the b-side of the induction step.
// ============================================================================

/// `sumRange (pascal_tail_term a b n) (succ n) = sumRange (pascal_tail_term a b n) n`
/// — the tail sum's own boundary term (at `k = n`) is zero, since
/// `choose n (succ n) = 0` (`choose_succ_self_eq_zero`).
fn u_tail_boundary(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let u_fn = pascal_tail_fn(d, a, b, n);
    let sn = d.succ(n);
    let start = d.sum_range(u_fn, sn);
    let sum_u_n = d.sum_range(u_fn, n);
    let u_n = pascal_tail_term(d, a, b, n, n);
    let mid0 = d.add(sum_u_n, u_n);
    let h_defeq = d.refl(mid0); // Eq(start, mid0) via sum_range_succ, definitional

    // u_n = mul(mul(choose(n,succ n), pow(a,succ n)), pow(b, sub(n,n))) = 0.
    // The congr steps must wrap BOTH the inner mul AND the outer mul that
    // `pascal_tail_term` builds, or they target the wrong (inner) subterm.
    let sn2 = d.succ(n);
    let c_n_sn = d.choose(n, sn2);
    let a_sn = d.pow(a, sn2);
    let sub_nn = d.sub(n, n);
    let b_pow_nn = d.pow(b, sub_nn);
    let zero = d.zero();

    let h_czero = d.lemma(p.choose_succ_self_eq_zero, &[n]); // c_n_sn = zero
    let zero_asn = d.mul(zero, a_sn);
    let mid_u1 = d.mul(zero_asn, b_pow_nn);
    let h1 = d.congr(c_n_sn, zero, h_czero, &|d, t| {
        let inner = d.mul(t, a_sn);
        d.mul(inner, b_pow_nn)
    });
    // h1 : Eq(u_n, mid_u1)

    let h_zm1 = d.lemma(p.zero_mul, &[a_sn]); // zero_asn = zero
    let mid_u2 = d.mul(zero, b_pow_nn);
    let h2 = d.congr(zero_asn, zero, h_zm1, &|d, t| d.mul(t, b_pow_nn));
    // h2 : Eq(mid_u1, mid_u2)

    let h_zm2 = d.lemma(p.zero_mul, &[b_pow_nn]); // mid_u2 = zero

    let (_e_u, u_zero_chain) = d.chain(u_n, &[(mid_u1, h1), (mid_u2, h2), (zero, h_zm2)]);
    // u_zero_chain : Eq(u_n, zero)

    let mid1 = d.add(sum_u_n, zero);
    let h3 = d.congr(u_n, zero, u_zero_chain, &|d, t| d.add(sum_u_n, t));
    let h_az = d.refl(sum_u_n); // Eq(mid1, sum_u_n) via add_zero, definitional

    let (_e, proof) = d.chain(start, &[(mid0, h_defeq), (mid1, h3), (sum_u_n, h_az)]);
    proof
}

/// `pascal_tail_term a b n k = b * binom_term a b n (succ k)`, for `k < n` —
/// needs `sub_succ_of_lt` (`k < n → sub n k = succ (sub n (succ k))`) to give
/// the `b`-exponent a successor shape, which `pow_succ` then peels into a
/// trailing `* b` matching the `mul_sum_range` reindex on the `b`-side.
fn b_side_term(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    k: ExprId,
    hlt: ExprId,
) -> ExprId {
    let p = *p;
    let sk = d.succ(k);
    let start = pascal_tail_term(d, a, b, n, k);

    let c = d.choose(n, sk);
    let ak = d.pow(a, sk);
    let c_ak = d.mul(c, ak);
    let sub_nk = d.sub(n, k);

    let sub_n_sk = d.sub(n, sk);
    let succ_sub_n_sk = d.succ(sub_n_sk);
    let h_lt = sub_succ_of_lt(d, &p, n, k, hlt); // sub_nk = succ_sub_n_sk
    let bpow_succ = d.pow(b, succ_sub_n_sk);
    let mid1 = d.mul(c_ak, bpow_succ);
    let h1 = d.congr(sub_nk, succ_sub_n_sk, h_lt, &|d, x| {
        let bp = d.pow(b, x);
        d.mul(c_ak, bp)
    });

    let bpow_n_sk = d.pow(b, sub_n_sk);
    let bpow_n_sk_b = d.mul(bpow_n_sk, b);
    let h_pow_succ = d.lemma(p.pow_succ, &[b, sub_n_sk]); // bpow_succ = bpow_n_sk_b
    let mid2 = d.mul(c_ak, bpow_n_sk_b);
    let h2 = d.congr(bpow_succ, bpow_n_sk_b, h_pow_succ, &|d, x| d.mul(c_ak, x));

    let term_n_sk = binom_term(d, a, b, n, sk); // = mul(c_ak, bpow_n_sk) exactly
    let term_n_sk_b = d.mul(term_n_sk, b);
    let h_assoc = d.lemma(p.mul_assoc, &[c_ak, bpow_n_sk, b]); // Eq(term_n_sk_b, mid2)
    let h3 = d.symm(term_n_sk_b, mid2, h_assoc);

    let b_term_n_sk = d.mul(b, term_n_sk);
    let h4 = d.lemma(p.mul_comm, &[term_n_sk, b]); // term_n_sk_b = b_term_n_sk

    let (_e, proof) = d.chain(
        start,
        &[(mid1, h1), (mid2, h2), (term_n_sk_b, h3), (b_term_n_sk, h4)],
    );
    proof
}

/// The `b`-side of the induction step:
/// `b * S(n) = pow b (succ n) + sumRange (pascal_tail_term a b n) n`.
///
/// Front-peels `S(n)` itself (`sum_range_shift_front`), distributes `b` over
/// the peeled front term and the tail sum (`left_distrib`), collapses
/// `b * term_n(0) = b * pow(b,n) = pow(b,succ n)`, and reindexes the tail via
/// [`b_side_term`] under `sum_range_congr_lt` (the ONLY sum in this
/// development whose pointwise hypothesis needs a bound) plus `mul_sum_range`.
fn b_side_lemma(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let sn = d.succ(n);
    let term_n_fn = binom_term_fn(d, a, b, n);
    let s_n = d.sum_range(term_n_fn, sn);
    let start = d.mul(b, s_n);

    let shifted_term_n_fn = shifted_fn(d, term_n_fn);
    let zero = d.zero();
    let term_n_0 = binom_term(d, a, b, n, zero);
    let tail_shifted_sum = d.sum_range(shifted_term_n_fn, n);
    let h_shift = d.lemma(p.sum_range_shift_front, &[term_n_fn, n]);
    // h_shift : Eq(s_n, add(term_n_0, tail_shifted_sum))
    let peeled = d.add(term_n_0, tail_shifted_sum);
    let mid1 = d.mul(b, peeled);
    let h1 = d.congr(s_n, peeled, h_shift, &|d, t| d.mul(b, t));

    let b_term_n0 = d.mul(b, term_n_0);
    let b_tail_shifted = d.mul(b, tail_shifted_sum);
    let distributed = d.add(b_term_n0, b_tail_shifted);
    let h2 = d.lemma(p.left_distrib, &[b, term_n_0, tail_shifted_sum]); // mid1 = distributed

    // term_n_0 = pow(b,n), so b * term_n_0 = b * pow(b,n) = pow(b,succ n).
    let pow_b_n = d.pow(b, n);
    let h_bnd = binom_term_zero_eq_pow_b(d, &p, a, b, n); // term_n_0 = pow_b_n
    let b_pow_b_n = d.mul(b, pow_b_n);
    let h3a = d.congr(term_n_0, pow_b_n, h_bnd, &|d, t| d.mul(b, t)); // b_term_n0 = b_pow_b_n
    let pow_b_sn = d.pow(b, sn);
    let h_comm = d.lemma(p.mul_comm, &[b, pow_b_n]); // b_pow_b_n = mul(pow_b_n,b)
    let pow_b_n_b = d.mul(pow_b_n, b);
    let h_pow_succ = d.lemma(p.pow_succ, &[b, n]); // pow_b_sn = pow_b_n_b
    let h3b = d.symm(pow_b_sn, pow_b_n_b, h_pow_succ); // pow_b_n_b = pow_b_sn
    let (_e3, b_term_n0_chain) = d.chain(
        b_term_n0,
        &[(b_pow_b_n, h3a), (pow_b_n_b, h_comm), (pow_b_sn, h3b)],
    );

    let mid2 = d.add(pow_b_sn, b_tail_shifted);
    let h3 = d.congr(b_term_n0, pow_b_sn, b_term_n0_chain, &|d, t| {
        d.add(t, b_tail_shifted)
    });

    // b * tail_shifted_sum = sumRange (pascal_tail_term a b n) n.
    let u_fn = pascal_tail_fn(d, a, b, n);
    let sum_u_n = d.sum_range(u_fn, n);

    let g_bounded = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let term_n_sk = binom_term(d, a, b, n, sk);
        let body = d.mul(b, term_n_sk);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, body)
    };
    let pointwise_lt = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hlt_ty = d.lt(k, n);
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);
        let body = b_side_term(d, &p, a, b, n, k, hlt);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, body);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, with_hlt)
    };
    let h_congr_lt = d.lemma(p.sum_range_congr_lt, &[u_fn, g_bounded, n, pointwise_lt]);
    // h_congr_lt : Eq(sum_u_n, sumRange g_bounded n)

    let h_msr = d.lemma(p.mul_sum_range, &[b, shifted_term_n_fn, n]);
    // h_msr : Eq(b_tail_shifted, sumRange g_bounded n) up to the definitional
    // match between `g_bounded` and `mul_sum_range`'s own scaled function.
    let sum_g_bounded_n = d.sum_range(g_bounded, n);
    let h_msr_via_congr_lt = d.symm(sum_u_n, sum_g_bounded_n, h_congr_lt);
    let h4 = d.trans(
        b_tail_shifted,
        sum_g_bounded_n,
        sum_u_n,
        h_msr,
        h_msr_via_congr_lt,
    );

    let final_target = d.add(pow_b_sn, sum_u_n);
    let h5 = d.congr(b_tail_shifted, sum_u_n, h4, &|d, t| d.add(pow_b_sn, t));

    let (_e, proof) = d.chain(
        start,
        &[
            (mid1, h1),
            (distributed, h2),
            (mid2, h3),
            (final_target, h5),
        ],
    );
    proof
}

// ============================================================================
// Stage 4: assembly.
// ============================================================================

/// The successor case of `add_pow`'s induction: given
/// `ih : (a+b)^n = S(n)`, prove `(a+b)^(succ n) = S(succ n)`.
fn add_pow_step(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = *p;
    let sn = d.succ(n);
    let ab = d.add(a, b);

    // LHS: pow(ab, succ n) --defeq--> mul(pow(ab,n), ab) --ih--> mul(S(n),ab)
    //   --left_distrib--> add(mul(S(n),a),mul(S(n),b)) --mul_comm x2-->
    //   add(mul(a,S(n)),mul(b,S(n))).
    let term_n_fn = binom_term_fn(d, a, b, n);
    let s_n = d.sum_range(term_n_fn, sn);
    let pow_ab_n = d.pow(ab, n);
    let start = d.pow(ab, sn);
    let mul_pow_ab = d.mul(pow_ab_n, ab);
    let h_start = d.refl(mul_pow_ab); // Eq(start, mul_pow_ab) via pow_succ, definitional

    let mul_sn_ab = d.mul(s_n, ab);
    let h_ih = d.congr(pow_ab_n, s_n, ih, &|d, t| d.mul(t, ab));

    let mul_sn_a = d.mul(s_n, a);
    let mul_sn_b = d.mul(s_n, b);
    let distributed = d.add(mul_sn_a, mul_sn_b);
    let h_ld = d.lemma(p.left_distrib, &[s_n, a, b]);

    let mul_a_sn = d.mul(a, s_n);
    let intermediate2 = d.add(mul_a_sn, mul_sn_b);
    let h_comm_a = d.lemma(p.mul_comm, &[s_n, a]);
    let h_ca = d.congr(mul_sn_a, mul_a_sn, h_comm_a, &|d, t| d.add(t, mul_sn_b));

    let mul_b_sn = d.mul(b, s_n);
    let w = d.add(mul_a_sn, mul_b_sn);
    let h_comm_b = d.lemma(p.mul_comm, &[s_n, b]);
    let h_cb = d.congr(mul_sn_b, mul_b_sn, h_comm_b, &|d, t| d.add(mul_a_sn, t));

    let (_e1, lhs_to_w) = d.chain(
        start,
        &[
            (mul_pow_ab, h_start),
            (mul_sn_ab, h_ih),
            (distributed, h_ld),
            (intermediate2, h_ca),
            (w, h_cb),
        ],
    );

    // RHS: S(succ n) = pow(b,succ n) + (a*S(n) + sumRange(U)(n))
    //                = a*S(n) + (pow(b,succ n) + sumRange(U)(n))  [add_left_comm]
    //                = a*S(n) + b*S(n) = w                        [b_side_lemma, symm]
    let term_sn_fn = binom_term_fn(d, a, b, sn);
    let ssn = d.succ(sn);
    let s_sn = d.sum_range(term_sn_fn, ssn);
    let zero = d.zero();
    let term_sn_0 = binom_term(d, a, b, sn, zero);
    let tail_sum = {
        let f = shifted_fn(d, term_sn_fn);
        d.sum_range(f, sn)
    };
    let h_shift_sn = d.lemma(p.sum_range_shift_front, &[term_sn_fn, sn]);
    // h_shift_sn : Eq(s_sn, add(term_sn_0, tail_sum))
    let peeled_sn = d.add(term_sn_0, tail_sum);

    let pow_b_sn = d.pow(b, sn);
    let h_bnd_sn = binom_term_zero_eq_pow_b(d, &p, a, b, sn); // term_sn_0 = pow_b_sn
    let mid_r1 = d.add(pow_b_sn, tail_sum);
    let h_r1 = d.congr(term_sn_0, pow_b_sn, h_bnd_sn, &|d, t| d.add(t, tail_sum));

    // Reuses `mul_a_sn`/`mul_b_sn` from the LHS chain above (not fresh
    // `mul(a,s_n)`/`mul(b,s_n)` copies) so the RHS chain lands on the
    // IDENTICAL expression `w`, with no separate bridge needed at the end.
    let sum_u_n = pascal_tail_fn(d, a, b, n);
    let sum_u_n_sn = d.sum_range(sum_u_n, sn);
    let h_a_side = a_side_lemma(d, &p, a, b, n); // Eq(tail_sum, add(mul_a_sn, sum_u_n_sn))
    let split_tail = d.add(mul_a_sn, sum_u_n_sn);
    let mid_r2 = d.add(pow_b_sn, split_tail);
    let h_r2 = d.congr(tail_sum, split_tail, h_a_side, &|d, t| d.add(pow_b_sn, t));

    let h_lcomm = add_left_comm(d, &p, pow_b_sn, mul_a_sn, sum_u_n_sn);
    let pow_b_sn_plus_u = d.add(pow_b_sn, sum_u_n_sn);
    let mid_r3 = d.add(mul_a_sn, pow_b_sn_plus_u);

    let sum_u_n_n = d.sum_range(sum_u_n, n);
    let h_u_bnd = u_tail_boundary(d, &p, a, b, n); // sum_u_n_sn = sum_u_n_n
    let b_sn_target = d.add(pow_b_sn, sum_u_n_n);
    let h_r3_inner = d.congr(sum_u_n_sn, sum_u_n_n, h_u_bnd, &|d, t| d.add(pow_b_sn, t));
    // h_r3_inner : Eq(pow_b_sn_plus_u, b_sn_target)
    let mid_r4 = d.add(mul_a_sn, b_sn_target);
    let h_r3 = d.congr(pow_b_sn_plus_u, b_sn_target, h_r3_inner, &|d, t| {
        d.add(mul_a_sn, t)
    });
    // h_r3 : Eq(mid_r3, mid_r4)

    let h_b_side = b_side_lemma(d, &p, a, b, n); // Eq(mul_b_sn, b_sn_target)
    let h_b_side_symm = d.symm(mul_b_sn, b_sn_target, h_b_side); // Eq(b_sn_target, mul_b_sn)

    let h_r4 = d.congr(b_sn_target, mul_b_sn, h_b_side_symm, &|d, t| {
        d.add(mul_a_sn, t)
    });
    // h_r4 : Eq(mid_r4, w)  -- `w = add(mul_a_sn, mul_b_sn)` exactly.

    let (_e2, rhs_to_w) = d.chain(
        s_sn,
        &[
            (peeled_sn, h_shift_sn),
            (mid_r1, h_r1),
            (mid_r2, h_r2),
            (mid_r3, h_lcomm),
            (mid_r4, h_r3),
            (w, h_r4),
        ],
    );

    let w_to_rhs = d.symm(s_sn, w, rhs_to_w);
    d.trans(start, w, s_sn, lhs_to_w, w_to_rhs)
}

/// `Nat.add_pow : ∀ a b n, (a+b)^n = sumRange (fun k => choose n k*a^k*b^(n-k)) (succ n)`
/// — the binomial theorem, by induction on `n`. The base case is a pure
/// computation (identical to [`declare_add_pow_sanity`]'s `add_pow_zero`); the
/// successor case is [`add_pow_step`], assembled from the `a`-side
/// ([`a_side_lemma`]), the `b`-side ([`b_side_lemma`]), and the reassociation
/// helpers ([`mul_left_comm`], [`add_left_comm`]).
pub(super) fn declare_add_pow(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let ab = d.add(a, b);
        let lhs = d.pow(ab, x);
        let rhs = binom_sum(d, a, b, x);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let ab = d.add(a, b);
            let zero = d.zero();
            let lhs = d.pow(ab, zero);
            d.refl(lhs)
        },
        &|d, j, ih| add_pow_step(d, &p, a, b, j, ih),
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_b = d.pi_fv(b_fv, nat, over_n);
        d.pi_fv(a_fv, nat, over_b)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_b = d.lam_fv(b_fv, nat, over_n);
        d.lam_fv(a_fv, nat, over_b)
    };
    d.declare_theorem(p.add_pow, ty, value)
}

/// `n=0` and `n=1` sanity instances of `add_pow`'s statement shape, proved
/// directly (no induction) — the smallest cases that already exercise the
/// same collapsing algebra (`one_mul`, `zero_add`, `add_comm`) the general
/// induction step needs, catching an off-by-one in the statement (the sum
/// bound, the exponent orientation) before it is spent on a much larger proof.
fn declare_add_pow_sanity(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // add_pow_zero : ∀ a b, (a+b)^0 = sumRange (fun k => choose 0 k*a^k*b^(0-k)) 1
    //
    // Every factor of the single term (k=0) collapses by pure computation —
    // `choose 0 0`, `a^0`, `b^(0-0)`, and `mul 1 1` are all literal — so this
    // closes by `refl` alone, with no lemma at all.
    d.theorem(p.add_pow_zero, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = d.add(a, b);
        let zero = d.zero();
        let lhs = d.pow(ab, zero);
        let rhs = binom_sum(d, a, b, zero);
        (d.eq(lhs, rhs), d.refl(lhs))
    })?;

    // add_pow_one : ∀ a b, (a+b)^1 = sumRange (fun k => choose 1 k*a^k*b^(1-k)) 2
    d.theorem(p.add_pow_one, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = d.add(a, b);
        let one = d.num(1);
        let lhs = d.pow(ab, one);
        let rhs = binom_sum(d, a, b, one);

        // lhs ~ mul(1,ab) [refl, pow_succ+pow_zero] -> ab [one_mul]
        let mul1_ab = d.mul(one, ab);
        let h_lhs1 = d.refl(mul1_ab);
        let h_lhs2 = d.lemma(p.one_mul, &[ab]);
        let lhs_to_ab = d.trans(lhs, mul1_ab, ab, h_lhs1, h_lhs2);

        // t0 = choose(1,0)*a^0*b^(1-0) ~ mul(1,mul(1,b)) [refl] -> mul(1,b) -> b
        let zero = d.zero();
        let t0 = binom_term(d, a, b, one, zero);
        let mul1_b = d.mul(one, b);
        let one_mul1b = d.mul(one, mul1_b);
        let h_bridge0 = d.refl(one_mul1b);
        let h_om1b = d.lemma(p.one_mul, &[mul1_b]);
        let h_om2b = d.lemma(p.one_mul, &[b]);
        let (_e0, t0_to_b) = d.chain(t0, &[(one_mul1b, h_bridge0), (mul1_b, h_om1b), (b, h_om2b)]);

        // t1 = choose(1,1)*a^1*b^(1-1) ~ add(zero,mul(1,mul(1,a))) [refl] -> mul(1,mul(1,a)) -> mul(1,a) -> a
        let t1 = binom_term(d, a, b, one, one);
        let mul1_a = d.mul(one, a);
        let one_mul1a = d.mul(one, mul1_a);
        let zero_plus = d.add(zero, one_mul1a);
        let h_bridge1 = d.refl(zero_plus);
        let h_za = d.lemma(p.zero_add, &[one_mul1a]);
        let h_om1a = d.lemma(p.one_mul, &[mul1_a]);
        let h_om2a = d.lemma(p.one_mul, &[a]);
        let (_e1, t1_to_a) = d.chain(
            t1,
            &[
                (zero_plus, h_bridge1),
                (one_mul1a, h_za),
                (mul1_a, h_om1a),
                (a, h_om2a),
            ],
        );

        // start := add(add(zero,t0),t1), def-eq `rhs` (pure ι/δ), -> ab
        let zero_t0 = d.add(zero, t0);
        let h_zt0 = d.lemma(p.zero_add, &[t0]);
        let zt0_to_b = d.trans(zero_t0, t0, b, h_zt0, t0_to_b);

        let start = d.add(zero_t0, t1);
        let add_b_t1 = d.add(b, t1);
        let h_start1 = d.congr(zero_t0, b, zt0_to_b, &|d, t| d.add(t, t1));
        let add_b_a = d.add(b, a);
        let h_start2 = d.congr(t1, a, t1_to_a, &|d, t| d.add(b, t));
        let h_comm = d.lemma(p.add_comm, &[b, a]);
        let (_e2, start_to_ab) = d.chain(
            start,
            &[(add_b_t1, h_start1), (add_b_a, h_start2), (ab, h_comm)],
        );

        let ab_to_start = d.symm(start, ab, start_to_ab);
        let final_proof = d.trans(lhs, ab, start, lhs_to_ab, ab_to_start);
        (d.eq(lhs, rhs), final_proof)
    })?;
    Ok(())
}

/// Declare `Nat.choose`'s finite-sum toolkit, the `n=0`/`n=1` sanity instances,
/// and the binomial theorem itself (`Nat.add_pow`). See the module docs for
/// the four-stage assembly.
pub(super) fn declare_binomial_theorem(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_sum_range_add(d, p)?;
    declare_sum_range_shift_front(d, p)?;
    declare_sum_range_congr_lt(d, p)?;
    declare_add_pow_sanity(d, p)?;
    declare_add_pow(d, p)?;
    Ok(())
}

// ============================================================================
// The row sum and the term bound.
//
// `sum_choose_row` takes the CHEAP route the module docs promise: instantiate
// `add_pow` at `a = b = 1`. Every `1^k` and `1^(n-k)` factor of the summand
// collapses via `one_pow` (built here — no existing lemma covers it), leaving
// exactly `sumRange (fun k => choose n k) (succ n)` on the left and
// `(1+1)^n`, definitionally `2^n` (`add`'s recursion is on its second
// argument, so `add 1 1` reduces to `2` by two `ι`-steps with no lemma
// needed), on the right.
//
// `choose_le_two_pow` is then the promised "immediate consequence" of the row
// sum plus "a term is at most the sum" — `le_sumRange_of_lt`, built here as a
// named reusable lemma since no prior module needed one. Its proof mirrors
// `choose_symm`'s successor case exactly: induct on the sum's bound with the
// index generalized inside the motive, and split the successor step on
// `lt_or_eq_of_le`.
//
// Vandermonde's convolution is NOT attempted here — see the doc comment on
// this section's end for the precise stall point.
// ============================================================================

/// `False.rec (fun _ => target) false_proof : target` — ex falso into an
/// arbitrary target from a proof of `False`. A local copy of
/// `order_more::ex_falso` (private to that module).
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `h : Le a b`, `heq : Eq b c ⊢ Le a c` — transport a `Le` fact along an
/// equality of its right-hand side. Built from the same generic
/// `eq_motive`/`transport` combinators `symm`/`trans`/`congr` are (`ops.rs`);
/// `Le` is just another `Nat`-indexed family they work uniformly over.
fn rewrite_le_rhs(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    heq: ExprId,
    h: ExprId,
) -> ExprId {
    let motive = d.eq_motive(b, &|d, x| d.le(a, x));
    d.transport(b, motive, h, c, heq)
}

/// `h : Le a b`, `heq : Eq a a2 ⊢ Le a2 b` — the left-hand-side counterpart of
/// [`rewrite_le_rhs`].
fn rewrite_le_lhs(
    d: &mut NatDev<'_>,
    a: ExprId,
    a2: ExprId,
    b: ExprId,
    heq: ExprId,
    h: ExprId,
) -> ExprId {
    let motive = d.eq_motive(a, &|d, x| d.le(x, b));
    d.transport(a, motive, h, a2, heq)
}

/// `fun k => choose n k`, as a lambda — the row-`n` function
/// [`declare_sum_choose_row`] and [`declare_choose_le_two_pow`] both state
/// their bound over, built once so the two theorems' instantiations line up
/// structurally.
fn choose_row_fn(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = d.choose(n, k);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Nat.one_pow : ∀ m, pow 1 m = 1`. `pow_zero`/`pow_succ` are both definitional
/// unfoldings, so the base case is `refl` and the successor case is `mul_one`
/// away from the induction hypothesis.
fn declare_one_pow(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.one_pow, 1, &|d, v| {
        let m = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let one = d.num(1);
            let lhs = d.pow(one, x);
            d.eq(lhs, one)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let one = d.num(1);
                d.refl(one)
            },
            &|d, j, ih| {
                let one = d.num(1);
                let sj = d.succ(j);
                let lhs = d.pow(one, sj);
                let pow_j = d.pow(one, j);
                let mul_pow_j_one = d.mul(pow_j, one);
                let h_start = d.refl(mul_pow_j_one); // pow_succ, definitional
                let mul_one_one = d.mul(one, one);
                let h_ih = d.congr(pow_j, one, ih, &|d, t| d.mul(t, one));
                let h_mul_one = d.lemma(p.mul_one, &[one]); // mul(1,1) = 1
                let (_e, proof) = d.chain(
                    lhs,
                    &[
                        (mul_pow_j_one, h_start),
                        (mul_one_one, h_ih),
                        (one, h_mul_one),
                    ],
                );
                proof
            },
            m,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.le_sumRange_of_lt : ∀ f n k, Lt k n → Le (f k) (sumRange f n)` — a
/// term inside a finite sum's range is at most the sum, by induction on `n`
/// with `k` generalized inside the motive (the same shape `choose_symm`
/// needs, for the same reason: the induction hypothesis must be usable at a
/// DIFFERENT `k` than the outer one). The successor case splits on
/// `lt_or_eq_of_le` exactly as `choose_symm`'s successor case does: the
/// strict branch extends the outer induction hypothesis past the new
/// boundary term via `le_add_right`/`le_trans`; the equal branch rewrites `f
/// k` to `f m` and reads the bound off `le_add_right` directly (after
/// commuting, since `le_add_right` only gives `a ≤ a+b`, not `b ≤ a+b`).
fn declare_le_sum_range_of_lt(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let stmt_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hyp = d.lt(k, x);
        let fk = d.apply(f, &[k]);
        let sx = d.sum_range(f, x);
        let concl = d.le(fk, sx);
        let body = d.arrow(hyp, concl);
        d.pi_fv(k_fv, nat, body)
    };
    let stmt = stmt_at(d, n);

    let proof = d.induct(
        &stmt_at,
        &|d| {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let zero = d.zero();
            let hyp_ty = d.lt(k, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let fk = d.apply(f, &[k]);
            let s0 = d.sum_range(f, zero);
            let target = d.le(fk, s0);
            let not_lt = d.lemma(p.not_lt_zero, &[k]);
            let false_proof = d.apply(not_lt, &[h]);
            let body = ex_falso(d, &p, target, false_proof);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(k_fv, nat, with_h)
        },
        &|d, m, ih| {
            let sm = d.succ(m);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hyp_ty = d.lt(k, sm);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // Lt k (succ m) is definitionally Le (succ k) (succ m);
            // le_of_succ_le_succ peels it to Le k m.
            let h_le_km = d.lemma(p.le_of_succ_le_succ, &[k, m, h]);
            let split = d.lemma(p.lt_or_eq_of_le, &[k, m, h_le_km]);

            let strict_ty = d.lt(k, m);
            let equal_ty = d.eq(k, m);
            let fk = d.apply(f, &[k]);
            let s_sm = d.sum_range(f, sm);
            let target = d.le(fk, s_sm);

            let s_m = d.sum_range(f, m);
            let fm = d.apply(f, &[m]);

            let minor_strict = {
                let hlt_fv = d.fresh_fvar();
                let hlt = d.kernel().fvar(hlt_fv);
                let ih_k = d.apply(ih, &[k, hlt]); // Le (f k) (sumRange f m)
                let ext = d.lemma(p.le_add_right, &[s_m, fm]); // Le(sumRange f m)(sumRange f m + f m)
                let body = d.lemma(p.le_trans, &[fk, s_m, s_sm, ih_k, ext]);
                d.lam_fv(hlt_fv, strict_ty, body)
            };
            let minor_equal = {
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);
                let fk_eq_fm = d.congr(k, m, heq, &|d, x| d.apply(f, &[x]));
                let h1 = d.lemma(p.le_add_right, &[fm, s_m]); // Le(f m)(f m + sumRange f m)
                let h_comm = d.lemma(p.add_comm, &[fm, s_m]); // f m+sumRange f m = sumRange f m+f m
                let add_fm_sm = d.add(fm, s_m);
                let add_sm_fm = d.add(s_m, fm);
                let h2 = rewrite_le_rhs(d, fm, add_fm_sm, add_sm_fm, h_comm, h1);
                let fm_eq_fk = d.symm(fk, fm, fk_eq_fm);
                let body = rewrite_le_lhs(d, fm, fk, add_sm_fm, fm_eq_fk, h2);
                d.lam_fv(heq_fv, equal_ty, body)
            };
            let selected = d.const_app(
                p.logic.or_elim,
                &[
                    strict_ty,
                    equal_ty,
                    target,
                    split,
                    minor_strict,
                    minor_equal,
                ],
            );
            let with_h = d.lam_fv(h_fv, hyp_ty, selected);
            d.lam_fv(k_fv, nat, with_h)
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
    d.declare_theorem(p.le_sum_range_of_lt, ty, value)
}

/// `Nat.sum_choose_row : ∀ n, sumRange (fun k => choose n k) (succ n) = pow 2 n`
/// — the row sum, via `add_pow` at `a = b = 1`.
fn declare_sum_choose_row(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.sum_choose_row, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let sn = d.succ(n);

        let f_one = binom_term_fn(d, one, one, n);
        let g = choose_row_fn(d, n);

        // Pointwise: choose n k * 1^k * 1^(n-k) = choose n k, for every k.
        let pointwise = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let c = d.choose(n, k);
            let ak = d.pow(one, k);
            let sub_nk = d.sub(n, k);
            let bk = d.pow(one, sub_nk);

            let start = binom_term(d, one, one, n, k);
            let h1 = d.lemma(p.one_pow, &[k]); // ak = one
            let c_one = d.mul(c, one);
            let mid1 = d.mul(c_one, bk);
            let h1c = d.congr(ak, one, h1, &|d, t| {
                let ct = d.mul(c, t);
                d.mul(ct, bk)
            });

            let h2 = d.lemma(p.mul_one, &[c]); // mul(c,1) = c
            let mid2 = d.mul(c, bk);
            let h2c = d.congr(c_one, c, h2, &|d, t| d.mul(t, bk));

            let h3 = d.lemma(p.one_pow, &[sub_nk]); // bk = one
            let mid3 = d.mul(c, one);
            let h3c = d.congr(bk, one, h3, &|d, t| d.mul(c, t));

            let h4 = d.lemma(p.mul_one, &[c]); // mul(c,1) = c

            let (_e, body) = d.chain(start, &[(mid1, h1c), (mid2, h2c), (mid3, h3c), (c, h4)]);
            let nat = d.nat_ty();
            d.lam_fv(k_fv, nat, body)
        };

        let h_congr = d.lemma(p.sum_range_congr, &[f_one, g, sn, pointwise]);
        // h_congr : sumRange f_one sn = sumRange g sn

        let h_add_pow = d.lemma(p.add_pow, &[one, one, n]);
        // h_add_pow : pow(add(one,one), n) = sumRange f_one sn

        let one_one = d.add(one, one);
        let pow_oo_n = d.pow(one_one, n);
        let sum_f_sn = d.sum_range(f_one, sn);
        let sum_g_sn = d.sum_range(g, sn);
        let (_e, forward) = d.chain(pow_oo_n, &[(sum_f_sn, h_add_pow), (sum_g_sn, h_congr)]);
        // forward : pow(one_one, n) = sumRange g sn

        let backward = d.symm(pow_oo_n, sum_g_sn, forward);
        // backward : sumRange g sn = pow(one_one, n) -- and add(one,one) is
        // definitionally 2 (add's recursion is on the second argument), so
        // this is accepted against the `pow(two, n)` statement below by def_eq.

        let stmt = {
            let lhs = d.sum_range(g, sn);
            let rhs = d.pow(two, n);
            d.eq(lhs, rhs)
        };
        (stmt, backward)
    })?;
    Ok(())
}

/// `Nat.choose_le_two_pow : ∀ n k, Le k n → Le (choose n k) (pow 2 n)` — a
/// binomial coefficient is at most `2^n`: `choose n k` is the sum's own term
/// at index `k` ([`declare_le_sum_range_of_lt`]), and the sum is `2^n`
/// ([`declare_sum_choose_row`]).
fn declare_choose_le_two_pow(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.choose_le_two_pow, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let two = d.num(2);
        let hyp_ty = d.le(k, n);
        let conclusion = {
            let c = d.choose(n, k);
            let bound = d.pow(two, n);
            d.le(c, bound)
        };
        let stmt = d.arrow(hyp_ty, conclusion);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let sn = d.succ(n);
        let h_lt = d.lemma(p.lt_succ_of_le, &[k, n, hyp]); // Lt k (succ n)

        let g = choose_row_fn(d, n);
        let h_bound = d.lemma(p.le_sum_range_of_lt, &[g, sn, k, h_lt]);
        // h_bound : Le (apply g k) (sumRange g sn) -- apply g k is defeq choose n k

        let h_row = d.lemma(p.sum_choose_row, &[n]); // sumRange g sn = pow(two, n)

        let ck = d.choose(n, k);
        let sum_g_sn = d.sum_range(g, sn);
        let pow_two_n = d.pow(two, n);
        let final_proof = rewrite_le_rhs(d, ck, sum_g_sn, pow_two_n, h_row, h_bound);

        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, final_proof);
        (stmt, with_hyp)
    })?;
    Ok(())
}

/// Declare the row sum, the term bound, and their shared toolkit
/// (`Nat.one_pow`, `Nat.le_sumRange_of_lt`).
///
/// # Vandermonde's convolution — not attempted; the precise stall point
///
/// `choose (m+n) k = sumRange (fun i => choose m i * choose n (k-i)) (succ k)`
/// needs an induction Pascal's rule alone cannot drive, and the reason is
/// worth recording exactly rather than re-discovering: `choose_succ_succ` is
/// unconditional (`choose (succ n)(succ j) = choose n j + choose n (succ j)`
/// for EVERY `n,j`, no case split), so the obstruction is not Pascal's rule
/// itself but getting the SECOND argument of `choose (succ n) (k-i)` into a
/// literal `succ _` shape — `sub` recurses on its second argument (`i` here),
/// so `sub (succ n) i` does not reduce for a bound `i`, unlike `sub n
/// (succ i)`, which peels for free.
///
/// The identity that supplies the missing successor shape IS now built —
/// [`declare_succ_sub_of_le`], `Nat.succ_sub_of_le`:
///
///   `succ_sub_of_le : Le i m → sub (succ m) i = succ (sub m i)`
///
/// (needed at `m := k'`, the induction's own bound, for every `i ≤ k'` inside
/// its sum), by [`succ_sub_of_le_proof`], mirroring
/// [`choose::sub_succ_of_lt`]'s use of `le_dest`: from `Le i m`, `le_dest`
/// gives a witness `j` with `add i j = m`. Substitute `m` by `add i j`. Then
/// `sub (succ (add i j)) i` is DEFINITIONALLY `sub (add i (succ j)) i` (`succ
/// (add i j) ≡ add i (succ j)` is just `add`'s own defining equation read
/// backwards), so `add_sub_cancel_left i (succ j)` gives it directly as
/// `succ j`; symmetrically `add_sub_cancel_left i j` gives `sub (add i j) i =
/// j`, so `succ (sub m i) = succ j` too. Both sides land on `succ j`;
/// `exists_rec` (as in `sub_succ_of_lt`) lifts the result from the witnessed
/// `add i j` back to the general `m`.
///
/// The assembly beyond it is NOT attempted here. With `succ_sub_of_le` in
/// hand, the outer induction (on `n`, `k`
/// generalized inside the motive as in [`declare_le_sum_range_of_lt`]) still
/// needs its successor case to split on `k = 0` vs `k = succ k'` (Pascal
/// needs the FIRST convolution index `k` succ-shaped too, and `k=0` has no
/// predecessor for the sum's own front term at `i=0`) — and `k=0` needs its
/// own one-term-sum collapse (`choose (succ(m+n)) 0 = 1`, matched against a
/// sum of length `1`), a smaller sibling of [`declare_add_pow_sanity`]'s
/// `n=0` case. The `k = succ k'` branch then reindexes a DOUBLE sum (both the
/// `m`-side index via Pascal and the `n`-side index via `succ_sub_of_le`),
/// the same shape of work [`a_side_lemma`]/[`b_side_lemma`] did for
/// `add_pow`, but with two independent shifts instead of one — sized
/// comparably to the whole binomial theorem, not a small addition to it.
pub(super) fn declare_combinatorial_identities(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_one_pow(d, p)?;
    declare_le_sum_range_of_lt(d, p)?;
    declare_sum_choose_row(d, p)?;
    declare_choose_le_two_pow(d, p)?;
    Ok(())
}

// ============================================================================
// Vandermonde's convolution — stage 1 only: `succ_sub_of_le`.
//
// The assembly (`k=0` base case, the `m`-side Pascal reindex, the `n`-side
// `succ_sub_of_le` reindex, and their combination) is NOT attempted here; see
// the doc comment on `declare_combinatorial_identities` above for exactly
// where it would continue and why it is sized comparably to `add_pow`.
// ============================================================================

/// `Le i m → sub (succ m) i = succ (sub m i)` — the proof term behind
/// [`declare_succ_sub_of_le`]/[`NatPrelude::succ_sub_of_le`].
///
/// Derived from `le_dest` exactly as [`super::choose::sub_succ_of_lt`] is:
/// `hle` gives a witness `j` with `add i j = m`. Substituting `m` by `add i
/// j`, `sub (succ (add i j)) i` is DEFINITIONALLY `sub (add i (succ j)) i`
/// (`succ (add i j) ≡ add i (succ j)` is `add`'s own defining equation read
/// backwards), so `add_sub_cancel_left i (succ j)` gives it directly as
/// `succ j`; symmetrically `add_sub_cancel_left i j` gives `sub (add i j) i =
/// j`, so `succ (sub m i) = succ j` too. Both sides land on `succ j`;
/// `exists_rec` lifts the result from the witnessed `add i j` back to the
/// general `m`.
fn succ_sub_of_le_proof(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    i: ExprId,
    hle: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();

    let represented = d.lemma(p.le_dest, &[i, m, hle]);
    let pred = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sum = d.add(i, j);
        let body = d.eq(sum, m);
        d.lam_fv(j_fv, nat, body)
    };

    let sm = d.succ(m);
    let target_lhs = d.sub(sm, i);
    let sub_mi = d.sub(m, i);
    let target_rhs = d.succ(sub_mi);
    let conclusion = d.eq(target_lhs, target_rhs);

    let represented_ty = {
        let one = d.level_one();
        let exists_ = d.kernel().const_(p.logic.exists_, vec![one]);
        d.apply(exists_, &[nat, pred])
    };
    let motive = d
        .kernel()
        .lam(anon, represented_ty, conclusion, BinderInfo::Default);

    let minor = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sum = d.add(i, j); // add i j
        let e_ty = d.eq(sum, m);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        // succ m = add i (succ j): succ(add i j) ≡ add i (succ j), definitionally.
        let succ_sum = d.succ(sum); // succ (add i j)
        let sj = d.succ(j);
        let add_i_sj = d.add(i, sj); // add i (succ j), defeq to succ_sum
        let h_congr_succ = d.congr(sum, m, e, &|d, x| d.succ(x)); // succ_sum = sm
        let h_bridge = d.refl(add_i_sj); // add_i_sj = succ_sum, via the defeq above
        let e2 = d.trans(add_i_sj, succ_sum, sm, h_bridge, h_congr_succ); // add_i_sj = sm

        // sub (add i (succ j)) i = succ j.
        let cancel_sj = d.lemma(p.add_sub_cancel_left, &[i, sj]);

        // Rewrite along e2 to land on sub (succ m) i = succ j.
        let sub_add_i_sj_i = d.sub(add_i_sj, i);
        let h_congr_sub = d.congr(add_i_sj, sm, e2, &|d, x| d.sub(x, i));
        let rev_congr_sub = d.symm(sub_add_i_sj_i, target_lhs, h_congr_sub);
        let target_lhs_eq_sj = d.trans(target_lhs, sub_add_i_sj_i, sj, rev_congr_sub, cancel_sj);

        // sub (add i j) i = j, transported along e to sub m i = j.
        let cancel_j = d.lemma(p.add_sub_cancel_left, &[i, j]);
        let sub_m_i_eq_j = {
            let motive2 = d.eq_motive(sum, &|d, x| {
                let s = d.sub(x, i);
                d.eq(s, j)
            });
            d.transport(sum, motive2, cancel_j, m, e)
        };

        // succ (sub m i) = succ j, i.e. target_rhs = sj.
        let target_rhs_eq_sj = d.congr(sub_mi, j, sub_m_i_eq_j, &|d, x| d.succ(x));
        let sj_eq_target_rhs = d.symm(target_rhs, sj, target_rhs_eq_sj);

        let final_ = d.trans(
            target_lhs,
            sj,
            target_rhs,
            target_lhs_eq_sj,
            sj_eq_target_rhs,
        );

        let with_e = d.lam_fv(e_fv, e_ty, final_);
        d.lam_fv(j_fv, nat, with_e)
    };

    let one = d.level_one();
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, pred, motive, minor, represented])
}

/// `Nat.succ_sub_of_le : ∀ m i, Le i m → sub (succ m) i = succ (sub m i)`. See
/// [`NatPrelude::succ_sub_of_le`] for the statement's role in Vandermonde's
/// convolution and [`succ_sub_of_le_proof`] for the derivation.
pub(super) fn declare_succ_sub_of_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.succ_sub_of_le, 2, &|d, v| {
        let (m, i) = (v[0], v[1]);
        let hyp_ty = d.le(i, m);
        let sm = d.succ(m);
        let lhs = d.sub(sm, i);
        let sub_mi = d.sub(m, i);
        let rhs = d.succ(sub_mi);
        let conclusion = d.eq(lhs, rhs);
        let stmt = d.arrow(hyp_ty, conclusion);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let body = succ_sub_of_le_proof(d, &p, m, i, hyp);
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, body);
        (stmt, with_hyp)
    })?;
    Ok(())
}

// ============================================================================
// The absorption identity: `Nat.succ_mul_choose_eq`.
//
// `(k+1) * choose (n+1) (k+1) = (n+1) * choose n k` — multiplying a row of
// Pascal's triangle by its column index reindexes it one row up. This is the
// algebraic half of `Nat.prime_dvd_choose` (`bezout.rs`); primality never
// enters here.
//
// Induction on `n`, generalized over `k` inside the motive. The successor
// step ALSO splits on `k` (Pascal needs a `succ` shape on that side too), so
// the whole proof is really a case tree of depth two: `n = 0`/`succ n`, and
// within the `succ n` step, `k = 0`/`succ k`. The `k = 0` sub-case of the
// successor step reads `choose (succ n) (succ 0) = succ n` off the outer IH
// at `k = 0` via `one_mul`; the `k = succ k'` sub-case uses the outer IH at
// both `k'` and `succ k'`, plus `succ_mul`/`left_distrib` to reassemble the
// two contributions into `succ (succ n) * choose (succ n) (succ k')`.
// ============================================================================

/// The `k = 0` case of [`succ_mul_choose_succ_all_k`]'s inner split: given the
/// outer induction hypothesis `ih : ∀ k, succ k * choose (succ n) (succ k) =
/// succ n * choose n k`, prove `succ zero * choose (succ (succ n)) (succ
/// zero) = succ (succ n) * choose (succ n) zero`.
fn succ_mul_choose_case_zero(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, ih: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let sz = d.succ(zero);
    let sn = d.succ(n);
    let ssn = d.succ(sn);
    let one = d.num(1);

    // RHS: succ(succ n) * choose (succ n) 0 = succ(succ n) * 1 = succ(succ n).
    let choose_sn_0 = d.choose(sn, zero);
    let c_sn_0 = d.lemma(p.choose_zero_right, &[sn]);
    let rhs0 = d.mul(ssn, choose_sn_0);
    let rhs_mid = d.mul(ssn, one);
    let rhs_step1 = d.congr(choose_sn_0, one, c_sn_0, &|d, t| d.mul(ssn, t));
    let rhs_step2 = d.lemma(p.mul_one, &[ssn]);
    let (_e, rhs_eq_ssn) = d.chain(rhs0, &[(rhs_mid, rhs_step1), (ssn, rhs_step2)]);

    // ih at 0, read through choose_zero_right + mul_one:
    // succ n * choose n zero = succ n * 1 = succ n.
    let choose_n_0 = d.choose(n, zero);
    let c_n_0 = d.lemma(p.choose_zero_right, &[n]);
    let ih0 = d.apply(ih, &[zero]);
    let ih0_rhs = d.mul(sn, choose_n_0);
    let ih0_rhs_mid = d.mul(sn, one);
    let ih0_step1 = d.congr(choose_n_0, one, c_n_0, &|d, t| d.mul(sn, t));
    let ih0_step2 = d.lemma(p.mul_one, &[sn]);
    let (_e2, ih0_rhs_eq_sn) = d.chain(ih0_rhs, &[(ih0_rhs_mid, ih0_step1), (sn, ih0_step2)]);

    let csn1 = d.choose(sn, sz);
    let ih0_lhs = d.mul(sz, csn1);
    // ih0 : ih0_lhs = ih0_rhs
    let (_e3, ih0_lhs_eq_sn) = d.chain(ih0_lhs, &[(ih0_rhs, ih0), (sn, ih0_rhs_eq_sn)]);

    // choose (succ n)(succ zero) = succ n, via one_mul cancelling the succ-zero coefficient.
    let one_mul_h = d.lemma(p.one_mul, &[csn1]);
    let ih0_lhs_eq_csn1 = d.symm(ih0_lhs, csn1, one_mul_h);
    let (_e4, csn1_eq_sn) = d.chain(csn1, &[(ih0_lhs, ih0_lhs_eq_csn1), (sn, ih0_lhs_eq_sn)]);

    // Pascal: choose (succ(succ n))(succ zero) = choose(succ n) zero + choose(succ n)(succ zero).
    let pascal = d.lemma(p.choose_succ_succ, &[sn, zero]);
    let c_ssn_sz = d.choose(ssn, sz);
    let sum0 = d.add(choose_sn_0, csn1);
    let step_a = d.congr(choose_sn_0, one, c_sn_0, &|d, t| d.add(t, csn1));
    let sum1 = d.add(one, csn1);
    let step_b = d.congr(csn1, sn, csn1_eq_sn, &|d, t| d.add(one, t));
    let sum2 = d.add(one, sn);

    // 1 + succ n = succ(succ n), via succ_add + zero_add.
    let succ_add_h = d.lemma(p.succ_add, &[zero, sn]);
    let zero_add_h = d.lemma(p.zero_add, &[sn]);
    let zero_plus_sn = d.add(zero, sn);
    let succ_zero_plus_sn = d.succ(zero_plus_sn);
    let zero_add_congr = d.congr(zero_plus_sn, sn, zero_add_h, &|d, t| d.succ(t));
    let (_e5, sum2_eq_ssn) = d.chain(
        sum2,
        &[(succ_zero_plus_sn, succ_add_h), (ssn, zero_add_congr)],
    );

    let (_e6, c_ssn_sz_eq_ssn) = d.chain(
        c_ssn_sz,
        &[
            (sum0, pascal),
            (sum1, step_a),
            (sum2, step_b),
            (ssn, sum2_eq_ssn),
        ],
    );

    // LHS: succ zero * choose(succ(succ n))(succ zero) = succ zero * succ(succ n) = succ(succ n).
    let lhs0 = d.mul(sz, c_ssn_sz);
    let lhs_mid = d.mul(sz, ssn);
    let lhs_step = d.congr(c_ssn_sz, ssn, c_ssn_sz_eq_ssn, &|d, t| d.mul(sz, t));
    let one_mul_ssn = d.lemma(p.one_mul, &[ssn]);
    let (_e7, lhs_eq_ssn) = d.chain(lhs0, &[(lhs_mid, lhs_step), (ssn, one_mul_ssn)]);

    let rhs_eq_ssn_rev = d.symm(rhs0, ssn, rhs_eq_ssn);
    let (_e8, proof) = d.chain(lhs0, &[(ssn, lhs_eq_ssn), (rhs0, rhs_eq_ssn_rev)]);
    proof
}

/// The `k = succ kp` case of [`succ_mul_choose_succ_all_k`]'s inner split:
/// given the outer IH `ih`, prove `succ(succ kp) * choose(succ(succ
/// n))(succ(succ kp)) = succ(succ n) * choose(succ n)(succ kp)`.
///
/// Pascal splits `choose(succ(succ n))(succ(succ kp))` into `X = choose(succ
/// n)(succ kp)` and `Y = choose(succ n)(succ(succ kp))`; `ih` at `kp` relates
/// `X` to `Z = choose n kp` and `ih` at `succ kp` relates `Y` to `W = choose n
/// (succ kp)` directly. `succ_mul` peels one copy of `X` off the `succ(succ
/// kp)` coefficient so the `Z`/`W` contributions combine via `left_distrib`
/// and Pascal's rule (read backwards) into `succ n * X`, and a final
/// `succ_mul` reassembles `succ n * X + X` into `succ(succ n) * X`.
fn succ_mul_choose_case_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    ih: ExprId,
    kp: ExprId,
) -> ExprId {
    let p = *p;
    let skp = d.succ(kp);
    let sskp = d.succ(skp);
    let sn = d.succ(n);
    let ssn = d.succ(sn);

    let x = d.choose(sn, skp);
    let y = d.choose(sn, sskp);
    let z = d.choose(n, kp);
    let w = d.choose(n, skp);

    // Pascal at (succ n, succ kp): choose(succ(succ n))(succ(succ kp)) = X + Y.
    let p1 = d.lemma(p.choose_succ_succ, &[sn, skp]);
    // Pascal at (n, kp): choose(succ n)(succ kp) = choose n kp + choose n (succ kp), i.e. X = Z+W.
    let p2 = d.lemma(p.choose_succ_succ, &[n, kp]);

    // ih at kp: succ kp * X = succ n * Z.
    let ih1 = d.apply(ih, &[kp]);
    // ih at succ kp: succ(succ kp) * Y = succ n * W.
    let ih2 = d.apply(ih, &[skp]);

    // T1: sskp*X = sn*Z + X, via succ_mul(skp,X) then rewriting skp*X by ih1.
    let succ_mul_skp_x = d.lemma(p.succ_mul, &[skp, x]);
    let skp_x = d.mul(skp, x);
    let sn_z = d.mul(sn, z);
    let sskp_x = d.mul(sskp, x);
    let skp_x_plus_x = d.add(skp_x, x);
    let sn_z_plus_x = d.add(sn_z, x);
    let ih1_congr = d.congr(skp_x, sn_z, ih1, &|d, t| d.add(t, x));
    let (_e1, t1) = d.chain(
        sskp_x,
        &[(skp_x_plus_x, succ_mul_skp_x), (sn_z_plus_x, ih1_congr)],
    );

    let sn_w = d.mul(sn, w);
    let c_ssn_sskp = d.choose(ssn, sskp);
    let start = d.mul(sskp, c_ssn_sskp);
    let xy = d.add(x, y);
    let sskp_xy = d.mul(sskp, xy);
    let sskp_y = d.mul(sskp, y);
    let sskp_x_plus_sskp_y = d.add(sskp_x, sskp_y);
    let sn_z_plus_x_plus_sskp_y = d.add(sn_z_plus_x, sskp_y);
    let sn_z_plus_x_plus_sn_w = d.add(sn_z_plus_x, sn_w);
    let x_plus_sn_w = d.add(x, sn_w);
    let sn_w_plus_x = d.add(sn_w, x);
    let sn_z_plus_open = d.add(sn_z, x_plus_sn_w);
    let sn_z_plus_swapped = d.add(sn_z, sn_w_plus_x);
    let sn_z_plus_sn_w = d.add(sn_z, sn_w);
    let sn_z_plus_sn_w_plus_x = d.add(sn_z_plus_sn_w, x);
    let zw = d.add(z, w);
    let sn_zw = d.mul(sn, zw);
    let sn_zw_plus_x = d.add(sn_zw, x);
    let sn_x = d.mul(sn, x);
    let sn_x_plus_x = d.add(sn_x, x);
    let ssn_x = d.mul(ssn, x);

    let step1 = d.congr(c_ssn_sskp, xy, p1, &|d, t| d.mul(sskp, t));
    let left_distrib_h = d.lemma(p.left_distrib, &[sskp, x, y]);
    let step3 = d.congr(sskp_x, sn_z_plus_x, t1, &|d, t| d.add(t, sskp_y));
    let step4 = d.congr(sskp_y, sn_w, ih2, &|d, t| d.add(sn_z_plus_x, t));
    let add_assoc1 = d.lemma(p.add_assoc, &[sn_z, x, sn_w]);
    let add_comm_h = d.lemma(p.add_comm, &[x, sn_w]);
    let step6 = d.congr(x_plus_sn_w, sn_w_plus_x, add_comm_h, &|d, t| d.add(sn_z, t));
    let add_assoc2 = d.lemma(p.add_assoc, &[sn_z, sn_w, x]);
    let step7 = d.symm(sn_z_plus_sn_w_plus_x, sn_z_plus_swapped, add_assoc2);
    let left_distrib2 = d.lemma(p.left_distrib, &[sn, z, w]);
    let left_distrib2_rev = d.symm(sn_zw, sn_z_plus_sn_w, left_distrib2);
    let step8 = d.congr(sn_z_plus_sn_w, sn_zw, left_distrib2_rev, &|d, t| {
        d.add(t, x)
    });
    let p2_rev = d.symm(x, zw, p2);
    let step9_inner = d.congr(zw, x, p2_rev, &|d, t| d.mul(sn, t));
    let step9 = d.congr(sn_zw, sn_x, step9_inner, &|d, t| d.add(t, x));
    let succ_mul_sn_x = d.lemma(p.succ_mul, &[sn, x]);
    let step10 = d.symm(ssn_x, sn_x_plus_x, succ_mul_sn_x);

    let (_e2, proof) = d.chain(
        start,
        &[
            (sskp_xy, step1),
            (sskp_x_plus_sskp_y, left_distrib_h),
            (sn_z_plus_x_plus_sskp_y, step3),
            (sn_z_plus_x_plus_sn_w, step4),
            (sn_z_plus_open, add_assoc1),
            (sn_z_plus_swapped, step6),
            (sn_z_plus_sn_w_plus_x, step7),
            (sn_zw_plus_x, step8),
            (sn_x_plus_x, step9),
            (ssn_x, step10),
        ],
    );
    proof
}

/// The successor step of [`declare_succ_mul_choose_eq`]'s outer induction on
/// `n`: given `ih : ∀ k, succ k * choose (succ n)(succ k) = succ n * choose n
/// k`, produce `∀ k, succ k * choose (succ(succ n))(succ k) = succ(succ n) *
/// choose (succ n) k`, by an inner case-split on `k`
/// ([`succ_mul_choose_case_zero`]/[`succ_mul_choose_case_succ`]).
fn succ_mul_choose_succ_all_k(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, ih: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let sn = d.succ(n);
    let ssn = d.succ(sn);

    let case_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let choose_ssn_sx = d.choose(ssn, sx);
        let lhs = d.mul(sx, choose_ssn_sx);
        let choose_sn_x = d.choose(sn, x);
        let rhs = d.mul(ssn, choose_sn_x);
        d.eq(lhs, rhs)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = d.induct(
        &case_motive,
        &|d| succ_mul_choose_case_zero(d, &p, n, ih),
        &|d, kp, _ih2| succ_mul_choose_case_succ(d, &p, n, ih, kp),
        k,
    );
    d.lam_fv(k_fv, nat, body)
}

/// The base case (`n = 0`) of [`declare_succ_mul_choose_eq`]'s outer
/// induction: `∀ k, succ k * choose (succ zero)(succ k) = succ zero * choose
/// zero k`, by a case-split on `k` alone (no induction hypothesis is needed
/// at `n = 0`).
fn succ_mul_choose_base_all_k(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let zero = d.zero();
    let sz = d.succ(zero);

    let case_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let choose_sz_sx = d.choose(sz, sx);
        let lhs = d.mul(sx, choose_sz_sx);
        let choose_zero_x = d.choose(zero, x);
        let rhs = d.mul(sz, choose_zero_x);
        d.eq(lhs, rhs)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = d.induct(
        &case_motive,
        &|d| {
            // k = 0: succ zero * choose(succ zero)(succ zero) = succ zero * choose zero zero,
            // both sides collapsing to succ zero * 1 via choose_self.
            let h1 = d.lemma(p.choose_self, &[sz]);
            let h2 = d.lemma(p.choose_self, &[zero]);
            let one = d.num(1);
            let choose_sz_sz = d.choose(sz, sz);
            let choose_zero_zero = d.choose(zero, zero);
            let lhs0 = d.mul(sz, choose_sz_sz);
            let rhs0 = d.mul(sz, choose_zero_zero);
            let mid = d.mul(sz, one);
            let step1 = d.congr(choose_sz_sz, one, h1, &|d, t| d.mul(sz, t));
            let step2 = d.congr(choose_zero_zero, one, h2, &|d, t| d.mul(sz, t));
            let step2_rev = d.symm(rhs0, mid, step2);
            let (_e, proof) = d.chain(lhs0, &[(mid, step1), (rhs0, step2_rev)]);
            proof
        },
        &|d, np, _ih| {
            // k = succ np: choose zero (succ np) = choose zero (succ (succ np)) = 0, and
            // Pascal collapses choose(succ zero)(succ(succ np)) to 0+0 = 0 too.
            let skp = d.succ(np);
            let sskp = d.succ(skp);
            let zero0 = d.zero();
            let zc1 = d.lemma(p.zero_choose_succ, &[np]);
            let zc2 = d.lemma(p.zero_choose_succ, &[skp]);
            let pascal = d.lemma(p.choose_succ_succ, &[zero0, skp]);

            let choose_zero_skp = d.choose(zero0, skp);
            let choose_zero_sskp = d.choose(zero0, sskp);
            let c_sz_sskp = d.choose(sz, sskp);
            let sum0 = d.add(choose_zero_skp, choose_zero_sskp);
            let sum1 = d.add(zero0, choose_zero_sskp);
            let sum2 = d.add(zero0, zero0);
            let step_a = d.congr(choose_zero_skp, zero0, zc1, &|d, t| {
                d.add(t, choose_zero_sskp)
            });
            let step_b = d.congr(choose_zero_sskp, zero0, zc2, &|d, t| d.add(zero0, t));
            let step_c = d.refl(zero0);
            let (_e, c_eq_zero) = d.chain(
                c_sz_sskp,
                &[
                    (sum0, pascal),
                    (sum1, step_a),
                    (sum2, step_b),
                    (zero0, step_c),
                ],
            );

            let lhs0 = d.mul(sskp, c_sz_sskp);
            let lhs_mid = d.mul(sskp, zero0);
            let mul_zero_sskp = d.lemma(p.mul_zero, &[sskp]);
            let lhs_step = d.congr(c_sz_sskp, zero0, c_eq_zero, &|d, t| d.mul(sskp, t));
            let (_e2, lhs_eq_zero) = d.chain(lhs0, &[(lhs_mid, lhs_step), (zero0, mul_zero_sskp)]);

            let rhs0 = d.mul(sz, choose_zero_skp);
            let rhs_mid = d.mul(sz, zero0);
            let mul_zero_sz = d.lemma(p.mul_zero, &[sz]);
            let rhs_step = d.congr(choose_zero_skp, zero0, zc1, &|d, t| d.mul(sz, t));
            let (_e3, rhs_eq_zero) = d.chain(rhs0, &[(rhs_mid, rhs_step), (zero0, mul_zero_sz)]);

            let rhs_eq_zero_rev = d.symm(rhs0, zero0, rhs_eq_zero);
            let (_e4, proof) = d.chain(lhs0, &[(zero0, lhs_eq_zero), (rhs0, rhs_eq_zero_rev)]);
            proof
        },
        k,
    );
    d.lam_fv(k_fv, nat, body)
}

/// `Nat.succ_mul_choose_eq : ∀ n k, succ k * choose (succ n)(succ k) = succ n * choose n k`.
///
/// See the module-level doc comment above for the proof shape.
pub(super) fn declare_succ_mul_choose_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let sn = d.succ(n);
        let choose_sn_sk = d.choose(sn, sk);
        let lhs = d.mul(sk, choose_sn_sk);
        let choose_n_k = d.choose(n, k);
        let rhs = d.mul(sn, choose_n_k);
        let eqn = d.eq(lhs, rhs);
        d.pi_fv(k_fv, nat, eqn)
    };

    d.theorem(p.succ_mul_choose_eq, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let sk = d.succ(k);
        let sn = d.succ(n);
        let choose_sn_sk = d.choose(sn, sk);
        let lhs = d.mul(sk, choose_sn_sk);
        let choose_n_k = d.choose(n, k);
        let rhs = d.mul(sn, choose_n_k);
        let stmt = d.eq(lhs, rhs);

        let all_k = d.induct(
            &motive,
            &|d| succ_mul_choose_base_all_k(d, &p),
            &|d, np, ih| succ_mul_choose_succ_all_k(d, &p, np, ih),
            n,
        );
        let proof = d.apply(all_k, &[k]);
        (stmt, proof)
    })?;
    Ok(())
}
