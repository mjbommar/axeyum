//! **ADR-1540's / ADR-1544's residue 3, and Eisenstein's lemma itself.**
//!
//! Three declarations, in dependency order:
//!
//! ```text
//! Nat.mul_sumRange_div_add_leastResidue : ∀ ap a m,
//!   Eq (mul a (sumRange succ m))
//!      (add (mul (succ ap) (sumRange (fun j => div (mul a (succ j)) (succ ap)) m))
//!           (sumRange (fun j => leastResidue (succ ap) a (succ j)) m))
//!
//! Nat.eisenstein_count_identity : ∀ m a, Eq (gcd a (succ (2*m))) 1 →
//!   Eq (add (mul a T) (add S S)) (add (mul pp (add F N)) T)
//!
//! Nat.eisenstein_lemma : ∀ m n, Eq (gcd (succ (2*n)) (succ (2*m))) 1 →
//!   Even (add F N)
//! ```
//!
//! with `pp := succ (2*m)`, `q := succ (2*n)`, `T := Σ_{j<m} (j+1)`,
//! `F := Σ_{j<m} ⌊a(j+1)/pp⌋`, `N := gaussNegCount pp a m`, and
//! `S := Σ_{j<m, sign j} gaussFold pp a (j+1)`.
//!
//! # What Eisenstein's lemma says here
//!
//! `Nat.Even (F + N)` is exactly `N ≡ Σ⌊qk/p⌋ (mod 2)`, which is what
//! quadratic reciprocity consumes: Gauss's lemma gives the Legendre symbol
//! as `(−1)^N`, and this replaces the counting exponent `N` by the floor sum
//! that `Nat.eisenstein_floor_sum` (ADR-1544 §2) can then pair with the
//! symmetric one. `Nat.Even x := ∃ k, x = k + k` (`parity.rs`), and over ℕ
//! `Even (F + N)` is equivalent to `F ≡ N (mod 2)`.
//!
//! **`Nat.modEq` DOES exist here** and the congruence form is declared too,
//! as `Nat.eisenstein_lemma_modEq`. Recording the check because a name
//! search misses it: `shape_search --name-like modEq` returns 40
//! declarations, every one of them `Int` — the `Nat` side spells its
//! theorems `mod_eq_*` (lower case) even though the constant they mention is
//! `Nat.modEq`, so the obvious query answers `Int` and looks conclusive. The
//! `Nat` definition is `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v`
//! (`modular.rs`), the BALANCED form, which is why the congruence is derived
//! from `Even` here rather than the other way round: the witnesses are
//! `u := N` and `v := k`, giving `F + 2·N = N + 2·k` from `F + N = k + k` by
//! one `add_comm`.
//!
//! # The three steps
//!
//! ## 1. The division algorithm, summed
//!
//! `a·k = pp·⌊a·k/pp⌋ + (a·k mod pp)` at every index, summed. The pointwise
//! fact is **already in this prelude and needed no new work**:
//! `Nat.div_mod_exec ap n : divMod (succ ap) n (div n (succ ap))
//! (mod n (succ ap))`, and `Nat.divMod d n q r` unfolds to
//! `And (Eq n (add (mul d q) r)) (Lt r d)` (`division.rs`), so its left
//! conjunct IS the division algorithm at a constructively positive divisor.
//! That is worth recording because a name search does not find it: there is
//! no `Nat.div_add_mod` in this prelude (measured ABSENT), and the identity
//! is reachable only through the relational `divMod` specification.
//!
//! Lifting it is `mul_sumRange` on the left, `sumRange_congr` in the middle,
//! `sumRange_add` and `mul_sumRange` on the right.
//!
//! ## 2. The counting identity
//!
//! Add step 1 to the residue/fold reconciliation
//! (`Nat.leastResidue_sumRange_reconcile`, residue 2) and the additive Gauss
//! bijection (`Nat.gauss_fold_sumRange_eq`, residue 1). The residue sum `Σ L`
//! appears on the right of step 1 and on the left of residue 2, so it
//! cancels by association alone — no subtraction anywhere:
//!
//! ```text
//! a·T + (S + S) = pp·F + ΣL + (S + S) = pp·F + (ΣG + pp·N)
//!               = pp·F + (T + pp·N)   = pp·(F + N) + T
//! ```
//!
//! Coprimality enters here and only here, through the bijection.
//!
//! ## 3. The parity read
//!
//! At `a := q = succ (2n)` the identity's two products lose their odd part
//! **definitionally**: `Nat.mul` recurses on its RIGHT argument, so after one
//! `mul_comm` the terms `mul T (succ (2n))` and `mul X (succ (2m))` ι-reduce
//! to `mul T (2n) + T` and `mul X (2m) + X` with no lemma at all. The `+ T`
//! on each side is then removed by `add_right_cancel`, leaving
//!
//! ```text
//! C + C = (B + B) + X       with  C := T·n + S,  B := X·m
//! ```
//!
//! and the parity of `X` follows by taking `mod _ 2` of both sides:
//! `add_mul_mod_self_left` deletes `B + B` on the right and `C + C` on the
//! left, `zero_mod` finishes, and `even_iff_mod_two_eq_zero` converts the
//! result to the existential `Nat.Even`.
//!
//! The doubling `x + x` is used throughout in preference to `2 * x` for the
//! reason residue 2 records: `mul 2 x` is stuck at a symbolic `x`. The one
//! place a `2 * x` must be produced (to feed `add_mul_mod_self_left`, whose
//! statement is `mod (a + b*c) b = mod a b`) goes through [`two_mul`] below,
//! a two-step local chain rather than a declaration.
//!
//! # What this does NOT prove
//!
//! **Quadratic reciprocity is not proved.** Eisenstein's lemma is one of its
//! two halves; the other is `Nat.eisenstein_floor_sum` (ADR-1544 §2), which
//! is already proved. What is missing between them is the ASSEMBLY: the two
//! must be combined at a pair of odd primes `p`, `q` with
//! `m = (p−1)/2`, `n = (q−1)/2`, and the resulting parity statement about
//! `N_p + N_q` must be turned into a statement about Legendre symbols
//! through `Int.gaussLemmaSignCount`. Both of those steps are `Int`-side and
//! neither is attempted here. See this lane's status file for the sized
//! remainder.

use super::NatPrelude;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps};
use super::parity::even_predicate;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `fun j => body(succ j)`, the one-based shift every index function shares.
fn shifted(d: &mut NatDev<'_>, body: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let sj = d.succ(j);
    let b = body(d, sj);
    d.lam_fv(j_fv, nat, b)
}

/// `fun j => succ j`.
fn succ_fn(d: &mut NatDev<'_>) -> ExprId {
    shifted(d, &|_d, k| k)
}

/// `Nat.mod x y` -- `NatOps` has no `mod` helper (its `mod_eq` family is the
/// CONGRUENCE `Nat.modEq`, a different thing), so the constant is applied
/// directly.
fn mod_of(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mod_, &[x, y])
}

/// `Eq (mul 2 x) (add x x)`.
///
/// Not a declaration: `mul x 2` ι-reduces to `add (add (mul x zero) x) x`
/// (`Nat.mul` recurses on its RIGHT argument), so the whole content is one
/// `mul_comm` and one `zero_add` under a congruence.
pub(super) fn two_mul(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p_ = *p;
    let two = d.num(2);
    let start = d.mul(two, x);
    let flipped = d.mul(x, two);
    let h1 = d.lemma(p_.mul_comm, &[two, x]);

    let zero = d.zero();
    let zero_add_x = d.add(zero, x);
    let target = d.add(x, x);
    let h2 = {
        let za = d.lemma(p_.zero_add, &[x]);
        d.congr(zero_add_x, x, za, &|d, t| d.add(t, x))
    };

    let (_end, proof) = d.chain(start, &[(flipped, h1), (target, h2)]);
    proof
}

// ===========================================================================
// Step 1: the division algorithm, summed.
// ===========================================================================

/// `Nat.mul_sumRange_div_add_leastResidue` — see this module's doc, step 1.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_mul_sum_range_div_add_least_residue(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.mul_sum_range_div_add_least_residue, 3, &|d, v| {
        let (ap, a, m) = (v[0], v[1], v[2]);
        let pp = d.succ(ap);

        let succ_f = succ_fn(d);
        let mul_fn = shifted(d, &|d, k| d.mul(a, k));
        let floor_fn = shifted(d, &|d, k| {
            let prod = d.mul(a, k);
            d.div(prod, pp)
        });
        let resid_fn = shifted(d, &|d, k| d.const_app(p.least_residue, &[pp, a, k]));
        let scaled_fn = shifted(d, &|d, k| {
            let prod = d.mul(a, k);
            let q = d.div(prod, pp);
            d.mul(pp, q)
        });
        let sum_fn = shifted(d, &|d, k| {
            let prod = d.mul(a, k);
            let q = d.div(prod, pp);
            let scaled = d.mul(pp, q);
            let r = d.const_app(p.least_residue, &[pp, a, k]);
            d.add(scaled, r)
        });

        // `∀ j, Eq (a * succ j) (pp * ⌊a·succ j/pp⌋ + leastResidue …)`, the
        // left conjunct of `divMod`'s own specification.
        let pointwise = {
            let nat = d.nat_ty();
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let num = d.mul(a, sj);
            let quot = d.div(num, pp);
            let scaled = d.mul(pp, quot);
            let r = d.const_app(p.least_residue, &[pp, a, sj]);
            let left = {
                let rhs = d.add(scaled, r);
                d.eq(num, rhs)
            };
            let right = d.lt(r, pp);
            let spec = d.lemma(p.div_mod_exec, &[ap, num]);
            let body = and_left(d, left, right, spec);
            d.lam_fv(j_fv, nat, body)
        };

        let t = d.sum_range(succ_f, m);
        let sum_mul = d.sum_range(mul_fn, m);
        let sum_sum = d.sum_range(sum_fn, m);
        let sum_scaled = d.sum_range(scaled_fn, m);
        let sum_resid = d.sum_range(resid_fn, m);
        let f_sum = d.sum_range(floor_fn, m);

        let start = d.mul(a, t);
        let h1 = d.lemma(p.mul_sum_range, &[a, succ_f, m]);
        let h2 = d.lemma(p.sum_range_congr, &[mul_fn, sum_fn, m, pointwise]);
        let step3 = d.add(sum_scaled, sum_resid);
        let h3 = d.lemma(p.sum_range_add, &[scaled_fn, resid_fn, m]);

        let pulled = d.mul(pp, f_sum);
        let target = d.add(pulled, sum_resid);
        let h4 = {
            let e = d.lemma(p.mul_sum_range, &[pp, floor_fn, m]);
            let back = d.symm(pulled, sum_scaled, e);
            d.congr(sum_scaled, pulled, back, &|d, t| d.add(t, sum_resid))
        };

        let (_end, proof) = d.chain(
            start,
            &[(sum_mul, h1), (sum_sum, h2), (step3, h3), (target, h4)],
        );
        let stmt = d.eq(start, target);
        (stmt, proof)
    })?;

    Ok(())
}

// ===========================================================================
// Step 2: the counting identity.
// ===========================================================================

/// `Nat.eisenstein_count_identity` — see this module's doc, step 2.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_eisenstein_count_identity(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.eisenstein_count_identity, 2, &|d, v| {
        let (m, a) = (v[0], v[1]);
        let two = d.num(2);
        let ap = d.mul(two, m);
        let pp = d.succ(ap);

        let one = d.num(1);
        let g = d.gcd(a, pp);
        let cop_ty = d.eq(g, one);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        let succ_f = succ_fn(d);
        let floor_fn = shifted(d, &|d, k| {
            let prod = d.mul(a, k);
            d.div(prod, pp)
        });
        let resid_fn = shifted(d, &|d, k| d.const_app(p.least_residue, &[pp, a, k]));
        let fold_fn = shifted(d, &|d, k| d.const_app(p.gauss_fold, &[pp, a, k]));
        let sign_fn = shifted(d, &|d, k| d.const_app(p.gauss_sign_neg, &[pp, a, k]));

        let t = d.sum_range(succ_f, m);
        let f_sum = d.sum_range(floor_fn, m);
        let l_sum = d.sum_range(resid_fn, m);
        let g_sum = d.sum_range(fold_fn, m);
        let n_count = d.const_app(p.gauss_neg_count, &[pp, a, m]);
        let s_sum = d.const_app(p.sum_range_if, &[sign_fn, fold_fn, m]);

        let doubled_s = d.add(s_sum, s_sum);
        let scaled_f = d.mul(pp, f_sum);
        let scaled_n = d.mul(pp, n_count);

        let start = {
            let lhs = d.mul(a, t);
            d.add(lhs, doubled_s)
        };

        // Step 1, at this modulus.
        let step1 = {
            let inner = d.add(scaled_f, l_sum);
            d.add(inner, doubled_s)
        };
        let h1 = {
            let e = d.lemma(p.mul_sum_range_div_add_least_residue, &[ap, a, m]);
            let lhs = d.mul(a, t);
            let rhs = d.add(scaled_f, l_sum);
            d.congr(lhs, rhs, e, &|d, x| d.add(x, doubled_s))
        };

        // Re-associate so the residue sum meets residue 2's own left side.
        let step2 = {
            let inner = d.add(l_sum, doubled_s);
            d.add(scaled_f, inner)
        };
        let h2 = d.lemma(p.add_assoc, &[scaled_f, l_sum, doubled_s]);

        // Residue 2.
        let step3 = {
            let inner = d.add(g_sum, scaled_n);
            d.add(scaled_f, inner)
        };
        let h3 = {
            let e = d.lemma(p.least_residue_sum_range_reconcile, &[ap, a, m]);
            let lhs = d.add(l_sum, doubled_s);
            let rhs = d.add(g_sum, scaled_n);
            d.congr(lhs, rhs, e, &|d, x| d.add(scaled_f, x))
        };

        // Residue 1: the fold sum IS the triangular sum, under coprimality.
        let step4 = {
            let inner = d.add(t, scaled_n);
            d.add(scaled_f, inner)
        };
        let h4 = {
            let e = d.lemma(p.gauss_fold_sum_range_eq, &[m, a, cop]);
            let back = d.symm(t, g_sum, e);
            d.congr(g_sum, t, back, &|d, x| {
                let inner = d.add(x, scaled_n);
                d.add(scaled_f, inner)
            })
        };

        let step5 = {
            let inner = d.add(scaled_n, t);
            d.add(scaled_f, inner)
        };
        let h5 = {
            let e = d.lemma(p.add_comm, &[t, scaled_n]);
            let lhs = d.add(t, scaled_n);
            let rhs = d.add(scaled_n, t);
            d.congr(lhs, rhs, e, &|d, x| d.add(scaled_f, x))
        };

        let step6 = {
            let inner = d.add(scaled_f, scaled_n);
            d.add(inner, t)
        };
        let h6 = {
            let fwd = d.lemma(p.add_assoc, &[scaled_f, scaled_n, t]);
            d.symm(step6, step5, fwd)
        };

        let combined = {
            let sum_fn_ = d.add(f_sum, n_count);
            d.mul(pp, sum_fn_)
        };
        let target = d.add(combined, t);
        let h7 = {
            let e = d.lemma(p.left_distrib, &[pp, f_sum, n_count]);
            let lhs = d.add(scaled_f, scaled_n);
            let back = d.symm(combined, lhs, e);
            d.congr(lhs, combined, back, &|d, x| d.add(x, t))
        };

        let (_end, body) = d.chain(
            start,
            &[
                (step1, h1),
                (step2, h2),
                (step3, h3),
                (step4, h4),
                (step5, h5),
                (step6, h6),
                (target, h7),
            ],
        );

        let concl = d.eq(start, target);
        let stmt = d.arrow(cop_ty, concl);
        let proof = d.lam_fv(cop_fv, cop_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}

// ===========================================================================
// Step 3: Eisenstein's lemma.
// ===========================================================================

/// `Nat.eisenstein_lemma` — see this module's doc, step 3.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
fn declare_eisenstein_lemma(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.eisenstein_lemma, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let two = d.num(2);
        let ap = d.mul(two, m);
        let pp = d.succ(ap);
        let aq = d.mul(two, n);
        let q = d.succ(aq);

        let one = d.num(1);
        let g = d.gcd(q, pp);
        let cop_ty = d.eq(g, one);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        let succ_f = succ_fn(d);
        let floor_fn = shifted(d, &|d, k| {
            let prod = d.mul(q, k);
            d.div(prod, pp)
        });
        let fold_fn = shifted(d, &|d, k| d.const_app(p.gauss_fold, &[pp, q, k]));
        let sign_fn = shifted(d, &|d, k| d.const_app(p.gauss_sign_neg, &[pp, q, k]));

        let t = d.sum_range(succ_f, m);
        let f_sum = d.sum_range(floor_fn, m);
        let n_count = d.const_app(p.gauss_neg_count, &[pp, q, m]);
        let s_sum = d.const_app(p.sum_range_if, &[sign_fn, fold_fn, m]);
        let x = d.add(f_sum, n_count);

        let doubled_s = d.add(s_sum, s_sum);
        let a_big = d.mul(t, n);
        let b_big = d.mul(x, m);
        let c_big = d.add(a_big, s_sum);

        // ---- from the counting identity to `C + C = (B + B) + X` ----------
        //
        // `mul q T` becomes `mul T q` by `mul_comm`, and `mul T (succ (2n))`
        // ι-reduces to `add (mul T (2n)) T` with no lemma -- `Nat.mul`
        // recurses on its RIGHT argument. Same on the other side.
        let identity = d.lemma(p.eisenstein_count_identity, &[m, q, cop]);

        let lhs_start = {
            let l = d.mul(q, t);
            d.add(l, doubled_s)
        };
        let rhs_start = {
            let r = d.mul(pp, x);
            d.add(r, t)
        };

        // LHS: `q*T + (S+S)` -> `((T*2n) + T) + (S+S)`.
        let lhs1 = {
            let inner = d.mul(t, aq);
            let l = d.add(inner, t);
            d.add(l, doubled_s)
        };
        let hl1 = {
            let from = d.mul(q, t);
            let to = d.mul(t, q);
            let e = d.lemma(p.mul_comm, &[q, t]);
            d.congr(from, to, e, &|d, z| d.add(z, doubled_s))
        };

        // `T*2n = A + A`.
        let lhs2 = {
            let inner = d.add(a_big, a_big);
            let l = d.add(inner, t);
            d.add(l, doubled_s)
        };
        let hl2 = {
            let from = d.mul(t, aq);
            let nn = d.add(n, n);
            let mid = d.mul(t, nn);
            let to = d.add(a_big, a_big);
            let e1 = {
                let tm = two_mul(d, &p, n);
                d.congr(aq, nn, tm, &|d, z| d.mul(t, z))
            };
            let e2 = d.lemma(p.left_distrib, &[t, n, n]);
            let e = d.trans(from, mid, to, e1, e2);
            d.congr(from, to, e, &|d, z| {
                let l = d.add(z, t);
                d.add(l, doubled_s)
            })
        };

        // `((A+A) + T) + (S+S)` -> `((A+A) + (S+S)) + T`.
        let lhs3 = {
            let inner = d.add(a_big, a_big);
            let l = d.add(inner, doubled_s);
            d.add(l, t)
        };
        let hl3 = {
            let aa = d.add(a_big, a_big);
            d.lemma(p.add_right_comm, &[aa, t, doubled_s])
        };

        // `(A+A) + (S+S)` -> `(A+S) + (A+S)` = `C + C`.
        let lhs4 = {
            let cc = d.add(c_big, c_big);
            d.add(cc, t)
        };
        let hl4 = {
            let aa = d.add(a_big, a_big);
            let from = d.add(aa, doubled_s);
            let to = d.add(c_big, c_big);
            let e = regroup_four(d, &p, a_big, a_big, s_sum, s_sum);
            d.congr(from, to, e, &|d, z| d.add(z, t))
        };

        // RHS: `pp*X + T` -> `((X*2m) + X) + T` -> `((B+B) + X) + T`.
        let rhs1 = {
            let inner = d.mul(x, ap);
            let r = d.add(inner, x);
            d.add(r, t)
        };
        let hr1 = {
            let from = d.mul(pp, x);
            let to = d.mul(x, pp);
            let e = d.lemma(p.mul_comm, &[pp, x]);
            d.congr(from, to, e, &|d, z| d.add(z, t))
        };
        let rhs2 = {
            let inner = d.add(b_big, b_big);
            let r = d.add(inner, x);
            d.add(r, t)
        };
        let hr2 = {
            let from = d.mul(x, ap);
            let mm = d.add(m, m);
            let mid = d.mul(x, mm);
            let to = d.add(b_big, b_big);
            let e1 = {
                let tm = two_mul(d, &p, m);
                d.congr(ap, mm, tm, &|d, z| d.mul(x, z))
            };
            let e2 = d.lemma(p.left_distrib, &[x, m, m]);
            let e = d.trans(from, mid, to, e1, e2);
            d.congr(from, to, e, &|d, z| {
                let r = d.add(z, x);
                d.add(r, t)
            })
        };

        // Chain the whole equation into `(C+C) + T = ((B+B)+X) + T`.
        let (_e_lhs, lhs_chain) = d.chain(
            lhs_start,
            &[(lhs1, hl1), (lhs2, hl2), (lhs3, hl3), (lhs4, hl4)],
        );
        let (_e_rhs, rhs_chain) = d.chain(rhs_start, &[(rhs1, hr1), (rhs2, hr2)]);

        let cc = d.add(c_big, c_big);
        let cc_t = d.add(cc, t);
        let bbx = {
            let bb = d.add(b_big, b_big);
            d.add(bb, x)
        };
        let bbx_t = d.add(bbx, t);

        // `(C+C)+T = q*T+(S+S) = pp*X+T = ((B+B)+X)+T`.
        let back_lhs = d.symm(lhs_start, cc_t, lhs_chain);
        let mid_eq = d.trans(cc_t, lhs_start, rhs_start, back_lhs, identity);
        let full = d.trans(cc_t, rhs_start, bbx_t, mid_eq, rhs_chain);

        // Cancel the trailing `T`.
        let cancelled = d.lemma(p.add_right_cancel, &[cc, bbx, t, full]);

        // ---- parity ------------------------------------------------------
        //
        // `mod X 2 = 0`, by deleting `B+B` from the right and `C+C` from the
        // left with `add_mul_mod_self_left`.
        let mod_x = {
            let two_v = d.num(2);
            mod_of(d, &p, x, two_v)
        };
        let two_b = {
            let two_v = d.num(2);
            d.mul(two_v, b_big)
        };
        let x_plus = d.add(x, two_b);
        let mod_x_plus = {
            let two_v = d.num(2);
            mod_of(d, &p, x_plus, two_v)
        };
        let hp1 = {
            let two_v = d.num(2);
            let e = d.lemma(p.add_mul_mod_self_left, &[x, two_v, b_big]);
            d.symm(mod_x_plus, mod_x, e)
        };

        let bb = d.add(b_big, b_big);
        let x_bb = d.add(x, bb);
        let mod_x_bb = {
            let two_v = d.num(2);
            mod_of(d, &p, x_bb, two_v)
        };
        let hp2 = {
            let tm = two_mul(d, &p, b_big);
            let inner = d.congr(two_b, bb, tm, &|d, z| d.add(x, z));
            d.congr(x_plus, x_bb, inner, &|d, z| {
                let two_v = d.num(2);
                mod_of(d, &p, z, two_v)
            })
        };

        let mod_bbx = {
            let two_v = d.num(2);
            mod_of(d, &p, bbx, two_v)
        };
        let hp3 = {
            let e = d.lemma(p.add_comm, &[x, bb]);
            d.congr(x_bb, bbx, e, &|d, z| {
                let two_v = d.num(2);
                mod_of(d, &p, z, two_v)
            })
        };

        let mod_cc = {
            let two_v = d.num(2);
            mod_of(d, &p, cc, two_v)
        };
        let hp4 = {
            let back = d.symm(cc, bbx, cancelled);
            d.congr(bbx, cc, back, &|d, z| {
                let two_v = d.num(2);
                mod_of(d, &p, z, two_v)
            })
        };

        let two_c = {
            let two_v = d.num(2);
            d.mul(two_v, c_big)
        };
        let mod_two_c = {
            let two_v = d.num(2);
            mod_of(d, &p, two_c, two_v)
        };
        let hp5 = {
            let tm = two_mul(d, &p, c_big);
            let back = d.symm(two_c, cc, tm);
            d.congr(cc, two_c, back, &|d, z| {
                let two_v = d.num(2);
                mod_of(d, &p, z, two_v)
            })
        };

        let zero = d.zero();
        let zero_plus = d.add(zero, two_c);
        let mod_zero_plus = {
            let two_v = d.num(2);
            mod_of(d, &p, zero_plus, two_v)
        };
        let hp6 = {
            let za = d.lemma(p.zero_add, &[two_c]);
            let back = d.symm(zero_plus, two_c, za);
            d.congr(two_c, zero_plus, back, &|d, z| {
                let two_v = d.num(2);
                mod_of(d, &p, z, two_v)
            })
        };

        let mod_zero = {
            let two_v = d.num(2);
            let z = d.zero();
            mod_of(d, &p, z, two_v)
        };
        let hp7 = {
            let two_v = d.num(2);
            let z = d.zero();
            d.lemma(p.add_mul_mod_self_left, &[z, two_v, c_big])
        };

        let zero_r = d.zero();
        let hp8 = {
            let two_v = d.num(2);
            d.lemma(p.zero_mod, &[two_v])
        };

        let (_e_par, parity) = d.chain(
            mod_x,
            &[
                (mod_x_plus, hp1),
                (mod_x_bb, hp2),
                (mod_bbx, hp3),
                (mod_cc, hp4),
                (mod_two_c, hp5),
                (mod_zero_plus, hp6),
                (mod_zero, hp7),
                (zero_r, hp8),
            ],
        );

        // `Even X` from `mod X 2 = 0`.
        let even_x = d.const_app(p.even, &[x]);
        let mod_stmt = {
            let z = d.zero();
            d.eq(mod_x, z)
        };
        let iff_lemma = d.lemma(p.even_iff_mod_two_eq_zero, &[x]);
        let mpr = d.const_app(p.logic.iff_mpr, &[even_x, mod_stmt, iff_lemma]);
        let body = d.apply(mpr, &[parity]);

        let stmt = d.arrow(cop_ty, even_x);
        let proof = d.lam_fv(cop_fv, cop_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}

// ===========================================================================
// The congruence form.
// ===========================================================================

/// `Nat.eisenstein_lemma_modEq : ∀ m n, Eq (gcd (succ (2*n)) (succ (2*m))) 1 →
/// modEq 2 F N` — Eisenstein's lemma as a congruence rather than as an
/// evenness.
///
/// `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v` (`modular.rs`) is the
/// BALANCED form, which makes this a two-line corollary rather than a second
/// proof: eliminate `Even (F + N)`'s witness `k` (so `F + N = k + k`), and
/// take `u := N`, `v := k`. Then `F + 2·N = (F + N) + N = (k + k) + N` and
/// `N + 2·k = N + (k + k)`, so the two sides differ by one `add_comm`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_eisenstein_lemma_mod_eq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.eisenstein_lemma_mod_eq, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let nat = d.nat_ty();
        let level_one = d.level_one();
        let two = d.num(2);
        let ap = d.mul(two, m);
        let pp = d.succ(ap);
        let aq = d.mul(two, n);
        let q = d.succ(aq);

        let one = d.num(1);
        let g = d.gcd(q, pp);
        let cop_ty = d.eq(g, one);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        let floor_fn = shifted(d, &|d, k| {
            let prod = d.mul(q, k);
            d.div(prod, pp)
        });
        let f_sum = d.sum_range(floor_fn, m);
        let n_count = d.const_app(p.gauss_neg_count, &[pp, q, m]);
        let x = d.add(f_sum, n_count);

        let target_ty = d.mod_eq(two, f_sum, n_count);
        let even_x = d.const_app(p.even, &[x]);
        let even_pred = even_predicate(d, x);
        let evidence = d.lemma(p.eisenstein_lemma, &[m, n, cop]);

        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let kk = d.add(k, k);
            let hk_ty = d.eq(x, kk);

            // `F + 2*N = (F + N) + N = (k + k) + N = N + (k + k) = N + 2*k`.
            let two_n = d.mul(two, n_count);
            let start = d.add(f_sum, two_n);
            let nn = d.add(n_count, n_count);
            let s1 = d.add(f_sum, nn);
            let e1 = {
                let tm = two_mul(d, &p, n_count);
                d.congr(two_n, nn, tm, &|d, z| d.add(f_sum, z))
            };
            let s2 = d.add(x, n_count);
            let e2 = {
                let fwd = d.lemma(p.add_assoc, &[f_sum, n_count, n_count]);
                d.symm(s2, s1, fwd)
            };
            let s3 = d.add(kk, n_count);
            let e3 = d.congr(x, kk, hk, &|d, z| d.add(z, n_count));
            let s4 = d.add(n_count, kk);
            let e4 = d.lemma(p.add_comm, &[kk, n_count]);
            let two_k = d.mul(two, k);
            let target = d.add(n_count, two_k);
            let e5 = {
                let tm = two_mul(d, &p, k);
                let back = d.symm(two_k, kk, tm);
                d.congr(kk, two_k, back, &|d, z| d.add(n_count, z))
            };
            let (_e, equation) = d.chain(
                start,
                &[(s1, e1), (s2, e2), (s3, e3), (s4, e4), (target, e5)],
            );

            let inner_pred = d.mod_eq_inner_predicate(two, f_sum, n_count, n_count);
            let outer_pred = d.mod_eq_outer_predicate(two, f_sum, n_count);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
            let inner = d.apply(intro, &[nat, inner_pred, k, equation]);
            let proof = d.apply(intro, &[nat, outer_pred, n_count, inner]);

            let with_hk = d.lam_fv(hk_fv, hk_ty, proof);
            d.lam_fv(k_fv, nat, with_hk)
        };

        let motive = {
            let anon = d.anon_name();
            d.kernel().lam(anon, even_x, target_ty, BinderInfo::Default)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
        let body = d.apply(rec, &[nat, even_pred, motive, minor, evidence]);

        let stmt = d.arrow(cop_ty, target_ty);
        let proof = d.lam_fv(cop_fv, cop_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}

/// `(a+b)+(c+e) = (a+c)+(b+e)` — originally a per-file-private copy of
/// `finite_set.rs`'s helper of the same shape. Exported (with [`two_mul`])
/// for `quadratic_reciprocity_count.rs`, which needs the same two moves and
/// would otherwise carry a third copy.
pub(super) fn regroup_four(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> ExprId {
    let p = *p;
    let ab = d.add(a, b);
    let ce = d.add(c, e);
    let start = d.add(ab, ce);

    let abc = d.add(ab, c);
    let step1 = d.add(abc, e);
    let h1 = {
        let fwd = d.lemma(p.add_assoc, &[ab, c, e]);
        d.symm(step1, start, fwd)
    };

    let ac = d.add(a, c);
    let acb = d.add(ac, b);
    let step2 = d.add(acb, e);
    let h2 = {
        let h_comm = d.lemma(p.add_right_comm, &[a, b, c]);
        d.congr(abc, acb, h_comm, &|d, x| d.add(x, e))
    };

    let be = d.add(b, e);
    let target = d.add(ac, be);
    let h3 = d.lemma(p.add_assoc, &[ac, b, e]);

    let (_end, proof) = d.chain(start, &[(step1, h1), (step2, h2), (target, h3)]);
    proof
}

/// Declare everything this module owns.
///
/// # Errors
///
/// Returns the trusted gate's rejection for the first declaration that does
/// not type-check.
pub(super) fn declare_eisenstein_lemma_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_mul_sum_range_div_add_least_residue(d, p)?;
    declare_eisenstein_count_identity(d, p)?;
    declare_eisenstein_lemma(d, p)?;
    declare_eisenstein_lemma_mod_eq(d, p)?;
    Ok(())
}
