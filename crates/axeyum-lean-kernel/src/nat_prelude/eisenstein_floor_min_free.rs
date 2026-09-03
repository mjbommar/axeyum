//! **ADR-1544's residue 5: the `min`-free form of `Nat.eisenstein_floor_sum`.**
//!
//! ```text
//! Nat.div_mul_succ_le_of_le : ∀ m n x, Le (succ x) m →
//!   Le (div (mul (succ (2*n)) (succ x)) (succ (2*m))) n
//!
//! Nat.eisenstein_floor_sum_min_free : ∀ m n,
//!   Eq (gcd (succ (2*m)) (succ (2*n))) 1 →
//!   Eq (add (sumRange (fun x => div (mul (succ (2*n)) (succ x)) (succ (2*m))) m)
//!           (sumRange (fun y => div (mul (succ (2*m)) (succ y)) (succ (2*n))) n))
//!      (mul n m)
//! ```
//!
//! # Why the `min` is there at all, and why it can come off HERE
//!
//! ADR-1290's floor lemma produces `Min.min n ⌊·⌋` because the row count of a
//! rectangle is capped by the rectangle's height, and ADR-1544 measured that
//! dropping the `min` from `Nat.eisenstein_floor_sum` is **REFUTED** at the
//! generality that theorem states (general coprime `pp`, `q`, unconstrained
//! `n`) and **SURVIVES** only at Eisenstein's own `m = (p−1)/2`,
//! `n = (q−1)/2`. That survivor is what this file turns into a theorem: at
//! `pp = 2m+1` and `q = 2n+1` the cap never binds, so the `min` really is
//! removable — but only after proving it, and the proof is a fact about those
//! two shapes, not about counting.
//!
//! # The arithmetic, and why it is not one line
//!
//! For `x < m` the bound is `q·(x+1) ≤ q·m < pp·(n+1)`, and the second
//! inequality is `2nm + m < 2mn + 2m + n + 1`, i.e. `0 < m + n + 1`. Trivial
//! on paper. What makes it work here is that **`mul q m` is stuck in both
//! directions**: `Nat.mul` recurses on its RIGHT argument, so `mul q m` with
//! `m` symbolic reduces to nothing, and `mul pp n` likewise. One `mul_comm`
//! on each turns them into `mul m (succ (2n))` and `mul n (succ (2m))`, which
//! ι-reduce to `mul m (2n) + m` and `mul n (2m) + n` — and the two leading
//! products are the same number `2mn` written two different ways, which takes
//! a nine-step chain through `mul_assoc`, `right_distrib` and `mul_comm` to
//! identify. Everything after that is `add_lt_add_left` and `succ_le_succ`.
//!
//! Every named lemma this file uses was checked present before it was
//! written: `Nat.div_lt_of_lt_mul`, `Nat.le_of_lt_succ`,
//! `Nat.mul_le_mul_left`, `Nat.lt_of_le_of_lt`, `Nat.add_lt_add_left`,
//! `Nat.le_add_right`, `Nat.succ_le_succ`, `Nat.min_eq_right`,
//! `Nat.right_distrib`, `Nat.mul_assoc`, `Nat.mul_comm`.
//!
//! # What this does NOT prove
//!
//! **Quadratic reciprocity is not proved.** This removes a `min` from one of
//! its two halves; the other half is `Nat.eisenstein_lemma` (ADR-1552) and
//! the assembly between them is not built.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Local shapes.
// ---------------------------------------------------------------------------

/// `body(from)` rewritten to `body(to)` along `h : Eq from to` — the generic
/// one-hole transport this file needs at `Le` and `Lt` positions, where
/// [`NatOps::congr`] (which is `Nat`-valued) does not apply.
fn rewrite(
    d: &mut NatDev<'_>,
    from: ExprId,
    to: ExprId,
    h: ExprId,
    refl_case: ExprId,
    body: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let motive = d.eq_motive(from, &|d, z| body(d, z));
    d.transport(from, motive, refl_case, to, h)
}

/// `Eq (mul 2 x) (add x x)`.
///
/// `mul x 2` ι-reduces to `add (add (mul x zero) x) x`, i.e. to
/// `add (add zero x) x`, so the whole content is one `mul_comm` and one
/// `zero_add` under a congruence.
/// Retired to the `simp` rewrite-chain producer (ADR-1586): a THIRD hand-
/// written copy of `Eq (mul 2 x) (add x x)`, beside `gauss_lemma.rs::
/// two_mul_eq_add` and `parity.rs::mul_two_eq_add_self`. The original hand
/// proof routed through `mul_comm` + `zero_add`; the producer finds a
/// different, equally valid, default-set-only path (`succ_mul` unfolds
/// twice, `zero_mul` then `zero_add` close it) — the hand proof's own
/// citations are not evidence of what the producer needs.
fn two_mul(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let two = d.num(2);
    let start = d.mul(two, x);
    let target = d.add(x, x);
    let rules = crate::simp::nat::default_rules(p);
    crate::simp::nat::prove_eq(d, &rules, start, target)
        .unwrap_or_else(|e| panic!("two_mul: simp declined: {e:?}"))
}

/// `Eq (mul a (mul 2 b)) (mul b (mul 2 a))` — the two spellings of `2ab`.
///
/// Nine steps, because neither side reduces: `mul a (mul 2 b)` is stuck on the
/// symbolic `mul 2 b`, so the identity has to be routed through
/// `mul (mul a 2) b`, `mul (add a a) b` and `right_distrib` to a sum of two
/// products, commuted, and folded back the other way.
fn two_mul_symm(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p_ = *p;
    let two = d.num(2);
    let two_b = d.mul(two, b);
    let start = d.mul(a, two_b);

    let a2 = d.mul(a, two);
    let s1 = d.mul(a2, b);
    let h1 = {
        let fwd = d.lemma(p_.mul_assoc, &[a, two, b]);
        d.symm(s1, start, fwd)
    };

    let aa = d.add(a, a);
    let s2 = d.mul(aa, b);
    let h2 = {
        let tm = two_mul(d, &p_, a);
        // `mul a 2` and `mul 2 a` are the same term up to `mul_comm`, and
        // `two_mul` already goes through it, so re-use it after one flip.
        let flip = d.lemma(p_.mul_comm, &[a, two]);
        let two_a = d.mul(two, a);
        let via = d.trans(a2, two_a, aa, flip, tm);
        d.congr(a2, aa, via, &|d, z| d.mul(z, b))
    };

    let ab = d.mul(a, b);
    let s3 = d.add(ab, ab);
    let h3 = d.lemma(p_.right_distrib, &[a, a, b]);

    let ba = d.mul(b, a);
    let s4 = d.add(ba, ab);
    let h4 = {
        let c = d.lemma(p_.mul_comm, &[a, b]);
        d.congr(ab, ba, c, &|d, z| d.add(z, ab))
    };
    let s5 = d.add(ba, ba);
    let h5 = {
        let c = d.lemma(p_.mul_comm, &[a, b]);
        d.congr(ab, ba, c, &|d, z| d.add(ba, z))
    };

    let bb = d.add(b, b);
    let s6 = d.mul(bb, a);
    let h6 = {
        let fwd = d.lemma(p_.right_distrib, &[b, b, a]);
        d.symm(s6, s5, fwd)
    };

    let b2 = d.mul(b, two);
    let s7 = d.mul(b2, a);
    let h7 = {
        let tm = two_mul(d, &p_, b);
        let flip = d.lemma(p_.mul_comm, &[b, two]);
        let two_b2 = d.mul(two, b);
        let via = d.trans(b2, two_b2, bb, flip, tm);
        let back = d.symm(b2, bb, via);
        d.congr(bb, b2, back, &|d, z| d.mul(z, a))
    };

    let two_a = d.mul(two, a);
    let target = d.mul(b, two_a);
    let h8 = d.lemma(p_.mul_assoc, &[b, two, a]);

    let (_end, proof) = d.chain(
        start,
        &[
            (s1, h1),
            (s2, h2),
            (s3, h3),
            (s4, h4),
            (s5, h5),
            (s6, h6),
            (s7, h7),
            (target, h8),
        ],
    );
    proof
}

/// `Le m (mul 2 m)`.
///
/// Retired to the `tactic` combinator (ADR-1589), same statement and same
/// route as `totient_dvd_chain::le_self_two_mul`: `simp`'s defaults rewrite
/// `mul 2 m` to `add m m`, `linarith` closes `Le m (add m m)` with no
/// hypotheses.
fn le_two_mul_self(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let p_ = *p;
    let two = d.num(2);
    let two_m = d.mul(two, m);
    let goal = d.le(m, two_m);
    let rules = crate::simp::nat::default_rules(&p_);
    let ctx = crate::tactic::Ctx {
        prelude: p_,
        assumptions: &[],
        rules: &rules,
    };
    let tactic = crate::tactic::Tactic::Then(
        Box::new(crate::tactic::Tactic::Simp),
        Box::new(crate::tactic::Tactic::Linarith),
    );
    crate::tactic::run(d, &ctx, &tactic, goal)
        .unwrap_or_else(|e| panic!("le_two_mul_self: Then(Simp, Linarith) declined: {e:?}"))
}

/// `Lt m (succ (mul 2 m))` — `eisenstein_floor_sum`'s bound hypothesis at the
/// Eisenstein shape, which is where it is free. Unchanged: `le_two_mul_self`
/// then `succ_le_succ`, the same composition as before its own leaf was
/// retired to the combinator.
fn lt_succ_two_mul_self(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let p_ = *p;
    let le = le_two_mul_self(d, &p_, m);
    let two = d.num(2);
    let two_m = d.mul(two, m);
    d.lemma(p_.succ_le_succ, &[m, two_m, le])
}

// ---------------------------------------------------------------------------
// `Nat.div_mul_succ_le_of_le`.
// ---------------------------------------------------------------------------

/// `Nat.div_mul_succ_le_of_le : ∀ m n x, Le (succ x) m →
/// Le (div (mul (succ (2*n)) (succ x)) (succ (2*m))) n`
///
/// See this module's doc for why the arithmetic is not one line.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
fn declare_div_mul_succ_le_of_le(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.div_mul_succ_le_of_le, 3, &|d, v| {
        let (m, n, x) = (v[0], v[1], v[2]);
        let two = d.num(2);
        let ap = d.mul(two, m);
        let pp = d.succ(ap);
        let aq = d.mul(two, n);
        let q = d.succ(aq);
        let sx = d.succ(x);
        let sn = d.succ(n);

        let hyp_ty = d.le(sx, m);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let prod = d.mul(q, sx);
        let quot = d.div(prod, pp);
        let concl = d.le(quot, n);

        // `A := mul m (2n)` and `B := mul n (2m)`, the two spellings of `2mn`.
        let a_big = d.mul(m, aq);
        let b_big = d.mul(n, ap);
        let h_ab = two_mul_symm(d, &p, m, n);

        let rhs_bound = d.mul(pp, sn);

        // `hle : Le m (add n (2*m))`.
        let hle = {
            let nm = d.add(n, m);
            let base = d.lemma(p.le_add_right, &[m, nm]);
            let s0 = d.add(m, nm);

            let mn = d.add(m, n);
            let s1 = d.add(mn, m);
            let e1 = {
                let fwd = d.lemma(p.add_assoc, &[m, n, m]);
                d.symm(s1, s0, fwd)
            };
            let s2 = d.add(nm, m);
            let e2 = {
                let c = d.lemma(p.add_comm, &[m, n]);
                d.congr(mn, nm, c, &|d, z| d.add(z, m))
            };
            let mm = d.add(m, m);
            let s3 = d.add(n, mm);
            let e3 = d.lemma(p.add_assoc, &[n, m, m]);
            let target = d.add(n, ap);
            let e4 = {
                let tm = two_mul(d, &p, m);
                let back = d.symm(ap, mm, tm);
                d.congr(mm, ap, back, &|d, z| d.add(n, z))
            };
            let (_e, chain) = d.chain(s0, &[(s1, e1), (s2, e2), (s3, e3), (target, e4)]);
            rewrite(d, s0, target, chain, base, &|d, z| d.le(m, z))
        };

        // `hm : Lt m (add n pp)` -- `add n pp` is `succ (add n (2m))` by iota,
        // so `succ_le_succ` lands on it directly.
        let n_ap = d.add(n, ap);
        let hm = d.lemma(p.succ_le_succ, &[m, n_ap, hle]);

        // `Lt (add B m) (add B (add n pp))`.
        let n_pp = d.add(n, pp);
        let step = d.lemma(p.add_lt_add_left, &[b_big, m, n_pp, hm]);

        // Re-associate the right operand to `add (add B n) pp`.
        let b_n = d.add(b_big, n);
        let assoc_rhs = {
            let fwd = d.lemma(p.add_assoc, &[b_big, n, pp]);
            let l = d.add(b_n, pp);
            let r = d.add(b_big, n_pp);
            d.symm(l, r, fwd)
        };
        let b_n_pp = d.add(b_n, pp);
        let b_m = d.add(b_big, m);
        let b_plus = d.add(b_big, n_pp);
        let step_assoc = rewrite(d, b_plus, b_n_pp, assoc_rhs, step, &|d, z| d.lt(b_m, z));

        // `add (add B n) pp` IS `add (mul n pp) pp` by iota; rewrite it to
        // `add (mul pp n) pp`, which IS `mul pp (succ n)` by iota.
        let n_pp_mul = d.mul(n, pp);
        let pp_n_mul = d.mul(pp, n);
        let comm_np = d.lemma(p.mul_comm, &[n, pp]);
        let step_rhs = rewrite(d, n_pp_mul, pp_n_mul, comm_np, step_assoc, &|d, z| {
            let r = d.add(z, pp);
            d.lt(b_m, r)
        });

        // Rewrite the left operand from `B` to `A`.
        let a_m = d.add(a_big, m);
        let back_ab = d.symm(a_big, b_big, h_ab);
        let step_lhs = rewrite(d, b_big, a_big, back_ab, step_rhs, &|d, z| {
            let l = d.add(z, m);
            d.lt(l, rhs_bound)
        });

        // `add A m` IS `mul m q` by iota; rewrite it to `mul q m`.
        let m_q = d.mul(m, q);
        let q_m = d.mul(q, m);
        let comm_qm = {
            let fwd = d.lemma(p.mul_comm, &[q, m]);
            d.symm(q_m, m_q, fwd)
        };
        let key = rewrite(d, m_q, q_m, comm_qm, step_lhs, &|d, z| d.lt(z, rhs_bound));
        let _ = a_m;

        // `Le (mul q (succ x)) (mul q m)`, then chain into the strict bound.
        let mono = d.lemma(p.mul_le_mul_left, &[q, sx, m, hyp]);
        let lt_prod = d.lemma(p.lt_of_le_of_lt, &[prod, q_m, rhs_bound, mono, key]);
        let lt_div = d.lemma(p.div_lt_of_lt_mul, &[prod, pp, sn, lt_prod]);
        let body = d.lemma(p.le_of_lt_succ, &[quot, n, lt_div]);

        let stmt = d.arrow(hyp_ty, concl);
        let proof = d.lam_fv(hyp_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}

// ---------------------------------------------------------------------------
// `Nat.eisenstein_floor_sum_min_free`.
// ---------------------------------------------------------------------------

/// `Nat.eisenstein_floor_sum_min_free` — see this module's doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_eisenstein_floor_sum_min_free(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.eisenstein_floor_sum_min_free, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let nat = d.nat_ty();
        let two = d.num(2);
        let ap = d.mul(two, m);
        let pp = d.succ(ap);
        let aq = d.mul(two, n);
        let q = d.succ(aq);

        let one = d.num(1);
        let g = d.gcd(pp, q);
        let cop_ty = d.eq(g, one);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        // The four summands: the two `min` forms the floor sum is stated at,
        // and the two bare floors this corollary states.
        let row_min = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let sx = d.succ(x);
            let prod = d.mul(q, sx);
            let quot = d.div(prod, pp);
            let body = d.const_app(p.min_min, &[n, quot]);
            d.lam_fv(x_fv, nat, body)
        };
        let row_bare = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let sx = d.succ(x);
            let prod = d.mul(q, sx);
            let body = d.div(prod, pp);
            d.lam_fv(x_fv, nat, body)
        };
        let col_min = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let sy = d.succ(y);
            let prod = d.mul(pp, sy);
            let quot = d.div(prod, q);
            let body = d.const_app(p.min_min, &[m, quot]);
            d.lam_fv(y_fv, nat, body)
        };
        let col_bare = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let sy = d.succ(y);
            let prod = d.mul(pp, sy);
            let body = d.div(prod, q);
            d.lam_fv(y_fv, nat, body)
        };

        let sum_row_min = d.sum_range(row_min, m);
        let sum_row_bare = d.sum_range(row_bare, m);
        let sum_col_min = d.sum_range(col_min, n);
        let sum_col_bare = d.sum_range(col_bare, n);

        // `∀ x, Lt x m → Eq (min n ⌊q(x+1)/pp⌋) ⌊q(x+1)/pp⌋`. `Lt x m` IS
        // `Le (succ x) m` definitionally, which is the bound lemma's own
        // hypothesis.
        let row_pointwise = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_ty = d.lt(x, m);
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let sx = d.succ(x);
            let prod = d.mul(q, sx);
            let quot = d.div(prod, pp);
            let bound = d.lemma(p.div_mul_succ_le_of_le, &[m, n, x, hx]);
            let body = d.lemma(p.min_eq_right, &[n, quot, bound]);
            let with_hx = d.lam_fv(hx_fv, hx_ty, body);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let col_pointwise = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let hy_ty = d.lt(y, n);
            let hy_fv = d.fresh_fvar();
            let hy = d.kernel().fvar(hy_fv);
            let sy = d.succ(y);
            let prod = d.mul(pp, sy);
            let quot = d.div(prod, q);
            let bound = d.lemma(p.div_mul_succ_le_of_le, &[n, m, y, hy]);
            let body = d.lemma(p.min_eq_right, &[m, quot, bound]);
            let with_hy = d.lam_fv(hy_fv, hy_ty, body);
            d.lam_fv(y_fv, nat, with_hy)
        };

        let row_eq = d.lemma(p.sum_range_congr_lt, &[row_min, row_bare, m, row_pointwise]);
        let col_eq = d.lemma(p.sum_range_congr_lt, &[col_min, col_bare, n, col_pointwise]);

        let bound_hyp = lt_succ_two_mul_self(d, &p, m);
        let base = d.lemma(p.eisenstein_floor_sum, &[ap, aq, m, n, cop, bound_hyp]);

        // `min` form -> bare form, then flip and chain onto the identity.
        let start = d.add(sum_row_min, sum_col_min);
        let mid = d.add(sum_row_bare, sum_col_min);
        let h1 = d.congr(sum_row_min, sum_row_bare, row_eq, &|d, z| {
            d.add(z, sum_col_min)
        });
        let target = d.add(sum_row_bare, sum_col_bare);
        let h2 = d.congr(sum_col_min, sum_col_bare, col_eq, &|d, z| {
            d.add(sum_row_bare, z)
        });
        let (_e, to_bare) = d.chain(start, &[(mid, h1), (target, h2)]);

        let product = d.mul(n, m);
        let back = d.symm(start, target, to_bare);
        let body = d.trans(target, start, product, back, base);

        let concl = d.eq(target, product);
        let stmt = d.arrow(cop_ty, concl);
        let proof = d.lam_fv(cop_fv, cop_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}

/// Declare everything this module owns.
///
/// Must run after `eisenstein_lattice.rs` (`Nat.eisenstein_floor_sum`).
///
/// # Errors
///
/// Returns the trusted gate's rejection for the first declaration that does
/// not type-check.
pub(super) fn declare_eisenstein_floor_min_free_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_div_mul_succ_le_of_le(d, p)?;
    declare_eisenstein_floor_sum_min_free(d, p)?;
    Ok(())
}
