//! The Catalan numbers.
//!
//! # Which definition, and why
//!
//! Two standard definitions exist. The RECURSIVE one (`C(0)=1`, `C(n+1) =
//! Σ_{i≤n} C(i)·C(n−i)`) is a course-of-values recursion — `C(n+1)` needs
//! EVERY earlier value, not just `C(n)` — so it cannot be built the way `fib`
//! was (a curried two-accumulator step); it would need a `Nat → Nat`-valued
//! motive carrying the whole prefix (the `testBitAux` device in
//! `binary.rs`), a substantial construction on its own.
//!
//! The CLOSED FORM needs no new recursion at all: `Nat.choose` already
//! exists, so
//!
//! ```text
//! Nat.catalan n := sub (choose (add n n) n) (choose (add n n) (succ n))
//! ```
//!
//! is a plain (non-recursive) definition, and `Nat.sub` is TOTAL (truncates
//! at zero), so this needs no safety proof to even be well-formed — unlike
//! the textbook `choose (2n) n / (n+1)`, which would route through `Nat.div`
//! (truncating) and require first showing `(n+1) ∣ choose (2n) n`.
//!
//! # Hand check before writing any kernel code
//!
//! `choose 0 0 = 1`, `choose 2 1 = 2`, `choose 2 2 = 1`, `choose 4 2 = 6`,
//! `choose 4 3 = 4`, `choose 6 3 = 20`, `choose 6 4 = 15`, `choose 8 4 = 70`,
//! `choose 8 5 = 56`, `choose 10 5 = 252`, `choose 10 6 = 210`. So:
//!
//! | `n` | `choose (2n) n` | `choose (2n) (n+1)` | `catalan n` |
//! |----:|----------------:|---------------------:|------------:|
//! |   0 |               1 |                    0 |           1 |
//! |   1 |               2 |                    1 |           1 |
//! |   2 |               6 |                    4 |           2 |
//! |   3 |              20 |                   15 |           5 |
//! |   4 |              70 |                   56 |          14 |
//! |   5 |             252 |                  210 |          42 |
//!
//! matching `C(0..5) = 1, 1, 2, 5, 14, 42` exactly.
//!
//! # `catalan_mul_succ`, and where the truncated subtraction goes
//!
//! `Nat.catalan_mul_succ : ∀ n, succ n * catalan n = choose (add n n) n` is
//! what makes `catalan` provably the Catalan numbers rather than an
//! arbitrary sequence that happens to share its first six values. Unfolding
//! the definition, this is
//!
//! ```text
//! succ n * (choose (2n) n - choose (2n) (n+1)) = choose (2n) n
//! ```
//!
//! and the truncated subtraction is handled by `Nat.mul_sub_left_distrib_total`
//! (UNCONDITIONAL: `b*(q-a) = b*q - b*a` for any `Nat`s, no `a ≤ q` hypothesis
//! needed) — so no separate "the subtraction doesn't truncate" lemma is
//! proved here at all; the identity that makes the final cancellation work,
//!
//! ```text
//! succ n * choose (2n) (n+1) = n * choose (2n) n      -- [`choose_center_ratio`]
//! ```
//!
//! is what actually carries the content, and it also happens to entail
//! `choose (2n) (n+1) ≤ choose (2n) n` as a byproduct (never stated
//! separately, since nothing here needs it in that form).
//!
//! `choose_center_ratio` is proved by a bare case split on `n` (the successor
//! case ignores its own induction hypothesis, `declare_choose_symm`'s
//! `k_cases` pattern), combining TWO instances of `Nat.succ_mul_choose_eq` —
//! at columns `n` and `n−1` of the ODD row `2n−1` — via `Nat.choose_symm`
//! showing those two columns of an odd row coincide (`(2n−1) − n = n−1`).
//! `Nat.choose_add_convolution` (Vandermonde) is NOT used: this is a
//! same-row ratio, not a convolution.
//!
//! # What is NOT attempted here
//!
//! The additive recurrence `catalan (succ n) = sumRange (fun i => catalan i *
//! catalan (n-i)) (succ n)` (Segner's recurrence) — proving the closed form
//! satisfies it — is priced but not built: it needs the RECURSIVE
//! definition's course-of-values apparatus (or an equivalent "strong
//! induction over the closed form" argument) on top of everything above, and
//! is a substantially larger, separable piece of work.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ============================================================================
// The definition.
// ============================================================================

/// `Nat.catalan n := sub (choose (add n n) n) (choose (add n n) (succ n))`.
/// Height 3: strictly greater than `choose`/`sub`/`add` (all height ≤ 2),
/// the only definitions it calls.
pub(super) fn declare_catalan(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let two_n = d.add(n, n);
    let a = d.choose(two_n, n);
    let sn = d.succ(n);
    let b = d.choose(two_n, sn);
    let body = d.sub(a, b);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.catalan,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(3),
    })?;
    Ok(())
}

// ============================================================================
// `catalan_mul_succ` and its private supporting lemma.
// ============================================================================

/// `add (succ np) (succ np) = succ (succ (add np np))` — usable (via defeq
/// on its own most-reduced left side) as a proof that `add (succ np) (succ
/// np)` equals `succ (succ (add np np))`. The FIRST `succ` is a bare
/// ι-reduction (`add`'s recursion is on its second argument, and that
/// argument is syntactically `succ np`); the second needs the actual
/// theorem `succ_add`, since `add (succ np) np`'s second argument is the
/// bare variable `np`, not syntactically `succ`-shaped.
/// Retired to the `simp` rewrite-chain producer (ADR-1586): `succ_add`
/// alone rewrites `mid` to `m_var` (a single default-set step), and the
/// outer `succ` wrap is one more `simp::nat::prove_eq` call over the wrapped
/// goal directly (the engine's own outermost-first descent finds the same
/// nested `succ_add` site under the extra `succ` and lifts it back up).
fn two_succ_eq(d: &mut NatDev<'_>, p: &NatPrelude, np: ExprId) -> ExprId {
    let snp = d.succ(np);
    let mid = d.add(snp, np); // add (succ np) np
    let a2 = d.add(np, np);
    let m_var = d.succ(a2); // succ (add np np)
    // Eq Nat (succ mid) (succ m_var); `succ mid` is definitionally
    // `add (succ np) (succ np)` by ι alone.
    let lhs = d.succ(mid);
    let rhs = d.succ(m_var);
    let rules = crate::simp::nat::default_rules(p);
    crate::simp::nat::prove_eq(d, &rules, lhs, rhs)
        .unwrap_or_else(|e| panic!("two_succ_eq: simp declined: {e:?}"))
}

/// The "opposite-of-center" ratio: `succ n * choose (add n n) (succ n) = n *
/// choose (add n n) n`. See the module doc for the two-`succ_mul_choose_eq`
/// derivation. Proved by a bare case split on `n` (the successor case
/// ignores its own induction hypothesis).
fn choose_center_ratio(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let two_x = d.add(x, x);
        let lhs = {
            let c = d.choose(two_x, sx);
            d.mul(sx, c)
        };
        let rhs = {
            let c = d.choose(two_x, x);
            d.mul(x, c)
        };
        d.eq(lhs, rhs)
    };
    d.induct(
        &motive,
        &|d| {
            // n = 0: `mul 1 (choose 0 1)` and `mul 0 (choose 0 0)` both
            // reduce to `0` by ι alone (see the module doc's hand check row
            // `n=0`).
            let zero = d.zero();
            d.refl(zero)
        },
        &|d, np, _ih| {
            let n_var = d.succ(np);
            let sn_var = d.succ(n_var);
            let a2 = d.add(np, np);
            let m_var = d.succ(a2); // 2n - 1
            let m2_var = d.succ(m_var); // "2n", in reduced form

            // Two instances of `succ_mul_choose_eq` over row `m_var`, at
            // columns `n_var` and `np`.
            let fact1 = d.lemma(p.succ_mul_choose_eq, &[m_var, n_var]);
            // fact1 : mul sn_var (choose m2_var sn_var) = mul m2_var (choose m_var n_var)
            let fact2 = d.lemma(p.succ_mul_choose_eq, &[m_var, np]);
            // fact2 : mul n_var (choose m2_var n_var) = mul m2_var (choose m_var np)

            // `sub m_var n_var = np`.
            let h_sub1 = d.lemma(p.succ_sub_succ, &[a2, np]); // sub m_var n_var = sub a2 np
            let h_sub2 = d.lemma(p.add_sub_cancel_left, &[np, np]); // sub a2 np = np
            let sub_mn = d.sub(m_var, n_var);
            let sub_a2np = d.sub(a2, np);
            let sub_eq = d.trans(sub_mn, sub_a2np, np, h_sub1, h_sub2);

            // `Le n_var m_var`.
            let h_le_np_a2 = d.lemma(p.le_add_right, &[np, np]); // Le np a2
            let h_le = d.lemma(p.le_succ_succ, &[np, a2, h_le_np_a2]); // Le n_var m_var

            // `choose m_var n_var = choose m_var np`.
            let h_symm = d.lemma(p.choose_symm, &[m_var, n_var, h_le]);
            // h_symm : choose m_var n_var = choose m_var sub_mn
            let choose_m_np = d.choose(m_var, np);
            let choose_m_submn = d.choose(m_var, sub_mn);
            let h_choose_np = d.congr(sub_mn, np, sub_eq, &|d, x| d.choose(m_var, x));
            // h_choose_np : choose m_var sub_mn = choose m_var np
            let choose_m_n = d.choose(m_var, n_var);
            let choose_eq = d.trans(choose_m_n, choose_m_submn, choose_m_np, h_symm, h_choose_np);
            // choose_eq : choose m_var n_var = choose m_var np

            let h_bridge = d.congr(choose_m_n, choose_m_np, choose_eq, &|d, x| d.mul(m2_var, x));
            // h_bridge : mul m2_var (choose m_var n_var) = mul m2_var (choose m_var np)

            let choose_m2_sn = d.choose(m2_var, sn_var);
            let l1 = d.mul(sn_var, choose_m2_sn);
            let r1 = d.mul(m2_var, choose_m_n);
            let r2 = d.mul(m2_var, choose_m_np);
            let choose_m2_n = d.choose(m2_var, n_var);
            let l2 = d.mul(n_var, choose_m2_n);

            let inner = d.trans(l1, r1, r2, fact1, h_bridge); // Eq l1 r2
            let fact2_rev = d.symm(l2, r2, fact2); // Eq r2 l2
            let final_m2 = d.trans(l1, r2, l2, inner, fact2_rev); // Eq l1 l2, in terms of m2_var

            // Rewrite `m2_var` to `add n_var n_var` (the motive's literal
            // form) via `two_succ_eq`.
            let two_n_var = d.add(n_var, n_var);
            let h2n = two_succ_eq(d, &p, np); // usable as Eq Nat two_n_var m2_var
            let h2n_rev = d.symm(two_n_var, m2_var, h2n); // usable as Eq Nat m2_var two_n_var

            let choose_2n_sn = d.choose(two_n_var, sn_var);
            let l1_twon = d.mul(sn_var, choose_2n_sn);
            let h_l1 = d.congr(m2_var, two_n_var, h2n_rev, &|d, x| {
                let c = d.choose(x, sn_var);
                d.mul(sn_var, c)
            });
            // h_l1 : l1 = l1_twon

            let choose_2n_n = d.choose(two_n_var, n_var);
            let l2_twon = d.mul(n_var, choose_2n_n);
            let h_l2 = d.congr(m2_var, two_n_var, h2n_rev, &|d, x| {
                let c = d.choose(x, n_var);
                d.mul(n_var, c)
            });
            // h_l2 : l2 = l2_twon

            let step_a = d.symm(l1, l1_twon, h_l1); // Eq l1_twon l1
            let step_b = d.trans(l1_twon, l1, l2, step_a, final_m2); // Eq l1_twon l2
            d.trans(l1_twon, l2, l2_twon, step_b, h_l2) // Eq l1_twon l2_twon
        },
        n,
    )
}

/// `Nat.catalan_mul_succ : ∀ n, mul (succ n) (catalan n) = choose (add n n)
/// n`. See the module doc for the shape.
pub(super) fn declare_catalan_mul_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.catalan_mul_succ, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);
        let two_n = d.add(n, n);
        let a = d.choose(two_n, n);
        let b = d.choose(two_n, sn);
        let cat_n = d.const_app(p.catalan, &[n]);

        let stmt = {
            let lhs = d.mul(sn, cat_n);
            d.eq(lhs, a)
        };

        // `mul sn (sub a b) = sub (mul sn a) (mul sn b)`, unconditionally.
        let distrib = d.lemma(p.mul_sub_left_distrib_total, &[sn, a, b]);
        // distrib : mul sn (sub a b) = sub (mul sn a) (mul sn b)

        let key = choose_center_ratio(d, &p, n); // mul sn b = mul n a

        let mul_sn_a = d.mul(sn, a);
        let mul_sn_b = d.mul(sn, b);
        let mul_n_a = d.mul(n, a);
        let h3 = d.congr(mul_sn_b, mul_n_a, key, &|d, x| d.sub(mul_sn_a, x));
        // h3 : sub (mul sn a) (mul sn b) = sub (mul sn a) (mul n a)

        // `sub (mul sn a) (mul n a) = a`, via `succ_mul` + `add_sub_cancel_left`.
        let h_succ_mul = d.lemma(p.succ_mul, &[n, a]); // mul sn a = add (mul n a) a
        let add_mna_a = d.add(mul_n_a, a);
        let h4a = d.congr(mul_sn_a, add_mna_a, h_succ_mul, &|d, x| d.sub(x, mul_n_a));
        // h4a : sub (mul sn a) (mul n a) = sub (add (mul n a) a) (mul n a)
        let h4b = d.lemma(p.add_sub_cancel_left, &[mul_n_a, a]);
        // h4b : sub (add (mul n a) a) (mul n a) = a
        let sub_mna_a = d.sub(add_mna_a, mul_n_a);
        let stage3 = d.sub(mul_sn_a, mul_n_a);
        let h4 = d.trans(stage3, sub_mna_a, a, h4a, h4b);
        // h4 : sub (mul sn a) (mul n a) = a

        let sub_ab = d.sub(a, b);
        let stage1 = d.mul(sn, sub_ab);
        let stage2 = d.sub(mul_sn_a, mul_sn_b);
        let step_ab = d.trans(stage1, stage2, stage3, distrib, h3);
        let result = d.trans(stage1, stage3, a, step_ab, h4);
        // result : mul sn (sub a b) = a, usable (via `catalan`'s δ/β-unfold)
        // as a proof of `mul sn (catalan n) = a`, i.e. `stmt`.

        (stmt, result)
    })?;
    Ok(())
}

/// Declare every theorem in this module.
pub(super) fn declare_catalan_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_catalan(d, p)?;
    declare_catalan_mul_succ(d, p)?;
    Ok(())
}
