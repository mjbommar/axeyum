//! `Nat.choose` — binomial coefficients, by structural two-argument
//! recursion, and Pascal's rule.
//!
//! `choose` is defined the way `Nat.beq` (`defs.rs`) and the executable
//! division state are: an OUTER `Nat.rec` on the first argument, whose motive
//! is the constant family `fun _ => Nat -> Nat` (a *row* of the triangle), and
//! whose successor case runs its own INNER `Nat.rec` on the second argument.
//! Both recursors eliminate into `Nat -> Nat`/`Nat` (`Sort 1`), so both use
//! the level-`1` instance of `Nat.rec`, exactly as `defs.rs` does.
//!
//! This gives three defining equations for free by ι-reduction alone — no
//! induction, no equation lemmas beyond a name to rewrite by:
//!   * `choose n 0 ≡ 1` reduces once `n` is a literal `zero`/`succ _`, so the
//!     *equation lemma* `choose_zero_right` (stated for a generic `n`) still
//!     needs induction, but each of its two cases is a bare `refl`.
//!   * `choose 0 (succ k) ≡ 0` and `choose (succ n) (succ k) ≡ choose n k +
//!     choose n (succ k)` (Pascal's rule) hold for a completely generic `n`/
//!     `k`, because the statement already supplies the `succ` shape the
//!     recursors need — both close by `refl` alone, exactly the "if the
//!     definition computes" case flagged for this slice.
//!
//! `choose_self`/`choose_succ_self_eq_zero` are proved together (the second
//! first, generalized over an offset so its own induction does not need the
//! other), and `choose_symm` is the first genuinely non-trivial identity,
//! proved by induction on `n` with the column `k` and its bound generalized
//! inside the motive (`sum_range_congr` in `algebra.rs` is the template for
//! this shape of induction), splitting the successor column into `k = 0`,
//! `k = n'` (the diagonal, via `choose_self`/`choose_zero_right`), and
//! `k < n'` (via a private helper that gives the truncated difference a
//! successor shape once it is known positive).
//!
//! No finite-sum operator is needed for any of this: [`NatPrelude::sum_range`]
//! already exists (`defs.rs`), so the binomial theorem's remaining gap is
//! elsewhere, not here.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use super::steps::absurd;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.choose n k`, by two-argument structural recursion: outer `Nat.rec` on
/// `n` produces a *row* `Nat -> Nat`; the zero row is `1` at column `0` and
/// `0` everywhere else, and the successor row's column `succ k` is
/// `priorRow k + priorRow (succ k)`, ignoring its own inner recursive value
/// (the recurrence never looks at the row it is building, only the row above
/// it) exactly as the executable division state's minors ignore an unused
/// division-derivation induction hypothesis (`defs.rs`).
pub(super) fn declare_choose(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);

    // Row for n = 0: column 0 is 1, every successor column is 0.
    let zero_minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let inner_motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
        let base = d.num(1);
        let step = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let zero = d.zero();
            let with_ih = d.lam_fv(ih_fv, nat, zero);
            d.lam_fv(j_fv, nat, with_ih)
        };
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[inner_motive, base, step, k]);
        d.lam_fv(k_fv, nat, body)
    };

    // Row for n = succ predecessor, given `ih : Nat -> Nat` (the prior row):
    // column 0 is 1, column succ j is `ih j + ih (succ j)`.
    let succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let inner_motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
        let base = d.num(1);
        let step = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let inner_ih_fv = d.fresh_fvar();
            let at_j = d.apply(ih, &[j]);
            let succ_j = d.succ(j);
            let at_succ_j = d.apply(ih, &[succ_j]);
            let sum = d.add(at_j, at_succ_j);
            let with_inner_ih = d.lam_fv(inner_ih_fv, nat, sum);
            d.lam_fv(j_fv, nat, with_inner_ih)
        };
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[inner_motive, base, step, k]);
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_ih = d.lam_fv(ih_fv, nat_to_nat, with_k);
        d.lam_fv(predecessor_fv, nat, with_ih)
    };

    let outer_motive = d.kernel().lam(anon, nat, nat_to_nat, BinderInfo::Default);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let rec = d.kernel().const_(p.rec, vec![one]);
    let row = d.apply(rec, &[outer_motive, zero_minor, succ_minor, n]);
    let applied = d.apply(row, &[k]);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, applied);
        d.lam_fv(n_fv, nat, with_k)
    };
    let ty = d.arrow(nat, nat_to_nat);
    // Strictly greater delta height than `add` (1), the only definition it calls.
    d.kernel().add_declaration(Declaration::Definition {
        name: p.choose,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;
    Ok(())
}

/// The three defining equations. `choose_zero_right` needs induction on `n`
/// (a bare free variable is not itself a constructor, so the outer recursor
/// is stuck until case-split), but both branches close by `refl`; the other
/// two hold for completely generic arguments because the statement already
/// supplies the `succ` shapes both recursors need.
pub(super) fn declare_choose_equations(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // choose_zero_right : ∀ n, choose n 0 = 1
    d.theorem(p.choose_zero_right, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let zero = d.zero();
            let lhs = d.choose(x, zero);
            let one = d.num(1);
            d.eq(lhs, one)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let lhs = d.choose(zero, zero);
                d.refl(lhs)
            },
            &|d, j, _ih| {
                let sj = d.succ(j);
                let zero = d.zero();
                let lhs = d.choose(sj, zero);
                d.refl(lhs)
            },
            n,
        );
        (stmt, proof)
    })?;

    // choose_succ_succ (Pascal's rule) :
    //   ∀ n k, choose (succ n) (succ k) = choose n k + choose n (succ k)
    d.theorem(p.choose_succ_succ, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let sn = d.succ(n);
        let sk = d.succ(k);
        let lhs = d.choose(sn, sk);
        let nk = d.choose(n, k);
        let n_sk = d.choose(n, sk);
        let rhs = d.add(nk, n_sk);
        (d.eq(lhs, rhs), d.refl(lhs))
    })?;

    // zero_choose_succ : ∀ k, choose 0 (succ k) = 0
    d.theorem(p.zero_choose_succ, 1, &|d, v| {
        let k = v[0];
        let sk = d.succ(k);
        let zero = d.zero();
        let lhs = d.choose(zero, sk);
        (d.eq(lhs, zero), d.refl(lhs))
    })?;

    Ok(())
}

/// `Eq.rec`-style combination: given `ha : a = 0` and `hb : b = 0`, produce
/// `add a b = 0`. `add x zero ≡ x` definitionally, so `add zero zero ≡ zero`
/// and the last link needs no lemma, only the defeq coercion.
fn combine_zero_sum(d: &mut NatDev<'_>, a: ExprId, b: ExprId, ha: ExprId, hb: ExprId) -> ExprId {
    let zero = d.zero();
    let start = d.add(a, b);
    let mid = d.add(zero, b);
    let h1 = d.congr(a, zero, ha, &|d, x| d.add(x, b));
    let end = d.add(zero, zero);
    let h2 = d.congr(b, zero, hb, &|d, x| d.add(zero, x));
    let (_end, proof) = d.chain(start, &[(mid, h1), (end, h2)]);
    proof
}

/// `choose_succ_self_eq_zero` and `choose_self`, proved in that order because
/// the first needs no lemma beyond Pascal's rule and defining equations,
/// while the second's inductive step needs the first at the same `n`.
pub(super) fn declare_choose_self(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // choose_succ_self_eq_zero : ∀ n, choose n (succ n) = 0
    //
    // Proved via the generalized `∀ j, choose n (succ (add n j)) = 0`
    // (instantiated at j = 0, where `add n 0 ≡ n` definitionally), so the
    // inductive step only ever needs the induction hypothesis at two POINTS
    // it already has universally quantified (`j` and `succ j`), rather than a
    // fact about a column one further out than anything the hypothesis
    // states.
    d.theorem(p.choose_succ_self_eq_zero, 1, &|d, v| {
        let n = v[0];

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sum = d.add(x, j);
            let s_sum = d.succ(sum);
            let lhs = d.choose(x, s_sum);
            let zero = d.zero();
            let eqn = d.eq(lhs, zero);
            d.pi_fv(j_fv, nat, eqn)
        };

        let all_j = d.induct(
            &motive,
            &|d| {
                // ∀ j, choose 0 (succ (add 0 j)) = 0 — reduces to 0 by pure
                // ι-reduction regardless of j, so every instance is `refl`.
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let zero = d.zero();
                let sum = d.add(zero, j);
                let s_sum = d.succ(sum);
                let lhs = d.choose(zero, s_sum);
                let body = d.refl(lhs);
                d.lam_fv(j_fv, nat, body)
            },
            &|d, np, ih| {
                // ih : ∀ j, choose np (succ (add np j)) = 0
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let snp = d.succ(np);

                let ih_j = d.apply(ih, &[j]);
                let sj = d.succ(j);
                let ih_sj = d.apply(ih, &[sj]);

                let m_j = d.add(np, j);
                let s_mj = d.succ(m_j);
                let ss_mj = d.succ(s_mj);
                let cnp_sm = d.choose(np, s_mj);
                let cnp_ssm = d.choose(np, ss_mj);

                let pascal = d.lemma(p.choose_succ_succ, &[np, s_mj]);
                let sum = d.add(cnp_sm, cnp_ssm);
                let combined = combine_zero_sum(d, cnp_sm, cnp_ssm, ih_j, ih_sj);
                let target_ssmj = d.choose(snp, ss_mj);
                let zero = d.zero();
                let fact_at_ssmj = d.trans(target_ssmj, sum, zero, pascal, combined);

                // Bridge `succ (succ (add np j))` back to `succ (add snp j)`
                // via the propositional `succ_add` (`add`'s recursion is on
                // its SECOND argument, so this direction is not definitional).
                let snp_j = d.add(snp, j);
                let succ_add_np_j = d.lemma(p.succ_add, &[np, j]);
                let e = d.congr(snp_j, s_mj, succ_add_np_j, &|d, x| d.succ(x));
                let succ_snp_j = d.succ(snp_j);
                let e_rev = d.symm(succ_snp_j, ss_mj, e);
                let motive2 = d.eq_motive(ss_mj, &|d, x| {
                    let c = d.choose(snp, x);
                    let zero = d.zero();
                    d.eq(c, zero)
                });
                let final_at_j = d.transport(ss_mj, motive2, fact_at_ssmj, succ_snp_j, e_rev);
                d.lam_fv(j_fv, nat, final_at_j)
            },
            n,
        );

        let zero = d.zero();
        let final_proof = d.apply(all_j, &[zero]);
        let sn = d.succ(n);
        let lhs = d.choose(n, sn);
        let zero2 = d.zero();
        (d.eq(lhs, zero2), final_proof)
    })?;

    // choose_self : ∀ n, choose n n = 1
    d.theorem(p.choose_self, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let cxx = d.choose(x, x);
            let one = d.num(1);
            d.eq(cxx, one)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let c00 = d.choose(zero, zero);
                d.refl(c00)
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let pascal = d.lemma(p.choose_succ_succ, &[j, j]);
                let cjj = d.choose(j, j);
                let cj_sj = d.choose(j, sj);
                let sum = d.add(cjj, cj_sj);
                let hzero = d.lemma(p.choose_succ_self_eq_zero, &[j]);
                let one = d.num(1);
                let mid = d.add(one, cj_sj);
                let h1 = d.congr(cjj, one, ih, &|d, t| d.add(t, cj_sj));
                let zero = d.zero();
                let end = d.add(one, zero);
                let h2 = d.congr(cj_sj, zero, hzero, &|d, t| d.add(one, t));
                let target = d.choose(sj, sj);
                let (_end, chain_proof) = d.chain(sum, &[(mid, h1), (end, h2)]);
                d.trans(target, sum, one, pascal, chain_proof)
            },
            n,
        );
        (stmt, proof)
    })?;

    Ok(())
}

/// `Lt k m → sub m k = succ (sub m (succ k))`, giving the truncated
/// difference a successor shape once it is known positive. Used only inside
/// `choose_symm`'s successor case (not exposed as a prelude lemma).
///
/// Derived from `le_dest` rather than by induction: `hlt` gives a witness `j`
/// with `add (succ k) j = m`, and `add_sub_cancel_left` reads off both
/// `sub m (succ k) = j` and `sub m k = succ j` from that one witness.
pub(super) fn sub_succ_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    k: ExprId,
    hlt: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let sk = d.succ(k);

    let represented = d.lemma(p.le_dest, &[sk, m, hlt]);
    let pred = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sum = d.add(sk, j);
        let body = d.eq(sum, m);
        d.lam_fv(j_fv, nat, body)
    };

    let target_lhs = d.sub(m, k);
    let sub_m_sk_expr = d.sub(m, sk);
    let target_rhs = d.succ(sub_m_sk_expr);
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
        let sum = d.add(sk, j);
        let e_ty = d.eq(sum, m);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        // m = succ (add k j)
        let kj = d.add(k, j);
        let succ_kj = d.succ(kj);
        let sum_eq_succ_kj = d.lemma(p.succ_add, &[k, j]);
        let sym_e = d.symm(sum, m, e);
        let m_eq_succ_kj = d.trans(m, sum, succ_kj, sym_e, sum_eq_succ_kj);
        let succ_kj_eq_m = d.symm(m, succ_kj, m_eq_succ_kj);

        // sub m (succ k) = j
        let cancel1 = d.lemma(p.add_sub_cancel_left, &[sk, j]);
        let sub_m_sk = {
            let motive = d.eq_motive(sum, &|d, x| {
                let s = d.sub(x, sk);
                d.eq(s, j)
            });
            d.transport(sum, motive, cancel1, m, e)
        };

        // sub m k = succ j
        let succ_j = d.succ(j);
        let k_succ_j = d.add(k, succ_j);
        let cancel2 = d.lemma(p.add_sub_cancel_left, &[k, succ_j]);
        let sub_m_k = {
            let motive = d.eq_motive(k_succ_j, &|d, x| {
                let s = d.sub(x, k);
                d.eq(s, succ_j)
            });
            d.transport(k_succ_j, motive, cancel2, m, succ_kj_eq_m)
        };

        // sub m k = succ (sub m (succ k)), from sub_m_k and sub_m_sk
        let congr_succ = d.congr(sub_m_sk_expr, j, sub_m_sk, &|d, x| d.succ(x));
        let succ_sub_m_sk = d.succ(sub_m_sk_expr);
        let rev = d.symm(succ_sub_m_sk, succ_j, congr_succ);
        let final_ = d.trans(target_lhs, succ_j, succ_sub_m_sk, sub_m_k, rev);

        let with_e = d.lam_fv(e_fv, e_ty, final_);
        d.lam_fv(j_fv, nat, with_e)
    };

    let one = d.level_one();
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, pred, motive, minor, represented])
}

/// `choose_symm`'s diagonal case: `k' = m`, so both sides of the target
/// equation independently reduce to `1` (`choose_self` / `choose_zero_right`
/// after `sub_self` collapses the difference to `0`).
fn choose_symm_case_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    k_prime: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let sm = d.succ(m);
    let sk = d.succ(k_prime);
    let lhs = d.choose(sm, sk);
    let one = d.num(1);

    let sm_sm = d.choose(sm, sm);
    let h_congr_lhs = d.congr(k_prime, m, heq, &|d, x| {
        let sx = d.succ(x);
        d.choose(sm, sx)
    });
    let h_self = d.lemma(p.choose_self, &[sm]);
    let (_e1, lhs_to_one) = d.chain(lhs, &[(sm_sm, h_congr_lhs), (one, h_self)]);

    let sub_sm_sk = d.sub(sm, sk);
    let rhs = d.choose(sm, sub_sm_sk);
    let sub_m_kprime = d.sub(m, k_prime);
    let h_sss = d.lemma(p.succ_sub_succ, &[m, k_prime]);
    let sub_m_m = d.sub(m, m);
    let h_congr_sub = d.congr(k_prime, m, heq, &|d, x| d.sub(m, x));
    let zero = d.zero();
    let h_subself = d.lemma(p.sub_self, &[m]);
    let (_e2, sub_to_zero) = d.chain(
        sub_sm_sk,
        &[
            (sub_m_kprime, h_sss),
            (sub_m_m, h_congr_sub),
            (zero, h_subself),
        ],
    );
    let choose_sm_zero = d.choose(sm, zero);
    let h_congr_rhs = d.congr(sub_sm_sk, zero, sub_to_zero, &|d, x| d.choose(sm, x));
    let h_czr = d.lemma(p.choose_zero_right, &[sm]);
    let (_e3, rhs_to_one) = d.chain(rhs, &[(choose_sm_zero, h_congr_rhs), (one, h_czr)]);

    let rev = d.symm(rhs, one, rhs_to_one);
    d.trans(lhs, one, rhs, lhs_to_one, rev)
}

/// `choose_symm`'s strict case: `k' < m`. Gives the difference `m - k'` a
/// successor shape via [`sub_succ_of_lt`], expands both `choose (succ m)
/// (succ k')` and `choose (succ m) (succ T)` (`T := m - succ k'`) by Pascal's
/// rule, and closes the resulting four-term equation with the outer
/// induction hypothesis applied at `k'` and at `succ k'` plus `add_comm`.
fn choose_symm_case_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    k_prime: ExprId,
    h2: ExprId,
    hlt: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = *p;
    let sm = d.succ(m);
    let sk = d.succ(k_prime);
    let lhs = d.choose(sm, sk);
    let sub_sm_sk = d.sub(sm, sk);
    let rhs = d.choose(sm, sub_sm_sk);

    let e1 = sub_succ_of_lt(d, &p, m, k_prime, hlt);
    let t = d.sub(m, sk);
    let succ_t = d.succ(t);

    let sub_m_kprime = d.sub(m, k_prime);
    let ss = d.lemma(p.succ_sub_succ, &[m, k_prime]);
    let (_e4, ss_e1) = d.chain(sub_sm_sk, &[(sub_m_kprime, ss), (succ_t, e1)]);

    // *1: ih(k', h2), rewritten along e1 (sub m k' = succ T).
    let star1 = d.apply(ih, &[k_prime, h2]);
    let choose_m_kprime = d.choose(m, k_prime);
    let choose_m_sub = d.choose(m, sub_m_kprime);
    let choose_m_succt = d.choose(m, succ_t);
    let h_c = d.congr(sub_m_kprime, succ_t, e1, &|d, x| d.choose(m, x));
    let (_e5, star1b) = d.chain(
        choose_m_kprime,
        &[(choose_m_sub, star1), (choose_m_succt, h_c)],
    );

    // *2: ih(succ k', hlt) — `sub m (succ k')` is `t` verbatim.
    let star2 = d.apply(ih, &[sk, hlt]);
    let choose_m_sk = d.choose(m, sk);
    let choose_m_t = d.choose(m, t);

    let pl = d.lemma(p.choose_succ_succ, &[m, k_prime]);
    let sum_l = d.add(choose_m_kprime, choose_m_sk);

    let pr = d.lemma(p.choose_succ_succ, &[m, t]);
    let sum_r = d.add(choose_m_t, choose_m_succt);

    let mid1 = d.add(choose_m_succt, choose_m_sk);
    let hc1 = d.congr(choose_m_kprime, choose_m_succt, star1b, &|d, x| {
        d.add(x, choose_m_sk)
    });
    let mid2 = d.add(choose_m_succt, choose_m_t);
    let hc2 = d.congr(choose_m_sk, choose_m_t, star2, &|d, x| {
        d.add(choose_m_succt, x)
    });
    let hcomm = d.lemma(p.add_comm, &[choose_m_succt, choose_m_t]);
    let (_e6, sum_l_to_sum_r) = d.chain(sum_l, &[(mid1, hc1), (mid2, hc2), (sum_r, hcomm)]);

    let choose_sm_succt = d.choose(sm, succ_t);
    let step1 = d.trans(lhs, sum_l, sum_r, pl, sum_l_to_sum_r);
    let rev_pr = d.symm(choose_sm_succt, sum_r, pr);
    let final_ = d.trans(lhs, sum_r, choose_sm_succt, step1, rev_pr);

    let congr_ss = d.congr(sub_sm_sk, succ_t, ss_e1, &|d, x| d.choose(sm, x));
    let rev_congr_ss = d.symm(rhs, choose_sm_succt, congr_ss);
    d.trans(lhs, choose_sm_succt, rhs, final_, rev_congr_ss)
}

/// `choose_symm : ∀ n k, k ≤ n → choose n k = choose n (n - k)`, by induction
/// on `n` with the column `k` and its bound generalized inside the motive
/// (the shape `sum_range_congr` in `algebra.rs` uses for the same reason: the
/// induction hypothesis must be usable at a DIFFERENT `k` than the outer
/// one). The successor case splits its own column argument into `0` and
/// `succ k'` via a nested induction (ignoring that induction's own
/// hypothesis — it is a case split, not a second recursion), and `succ k'`
/// splits again into `k' = m` and `k' < m` via `lt_or_eq_of_le`.
pub(super) fn declare_choose_symm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hyp = d.le(k, n);
        let lhs = d.choose(n, k);
        let sub_nk = d.sub(n, k);
        let rhs = d.choose(n, sub_nk);
        let eqn = d.eq(lhs, rhs);
        let body = d.arrow(hyp, eqn);
        d.pi_fv(k_fv, nat, body)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_n = stmt_at(d, n);

    let proof = d.induct(
        &stmt_at,
        &|d| {
            // fun k (h : Le k 0) => choose 0 k = choose 0 (sub 0 k)
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let zero = d.zero();
            let hyp_ty = d.le(k, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let zk = d.lemma(p.zero_le, &[k]);
            let heq0 = d.lemma(p.le_antisymm, &[k, zero, h, zk]);
            let sym_heq0 = d.symm(k, zero, heq0);
            let motive = d.eq_motive(zero, &|d, x| {
                let zero = d.zero();
                let c1 = d.choose(zero, x);
                let sub0x = d.sub(zero, x);
                let c2 = d.choose(zero, sub0x);
                d.eq(c1, c2)
            });
            let base_val = {
                let zero = d.zero();
                let c00 = d.choose(zero, zero);
                d.refl(c00)
            };
            let body = d.transport(zero, motive, base_val, k, sym_heq0);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(k_fv, nat, with_h)
        },
        &|d, m, ih| {
            // fun k (h : Le k (succ m)) => choose (succ m) k = choose (succ m) (sub (succ m) k)
            let sm = d.succ(m);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let inner_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let hyp = d.le(x, sm);
                let lhs = d.choose(sm, x);
                let subv = d.sub(sm, x);
                let rhs = d.choose(sm, subv);
                let eqn = d.eq(lhs, rhs);
                d.arrow(hyp, eqn)
            };
            let k_cases = d.induct(
                &inner_motive,
                &|d| {
                    // fun (_ : Le 0 (succ m)) => choose (succ m) 0 = choose (succ m) (sub (succ m) 0)
                    let zero = d.zero();
                    let hyp_ty = d.le(zero, sm);
                    let h_fv = d.fresh_fvar();
                    let lhs = d.choose(sm, zero);
                    let one = d.num(1);
                    let h_czr = d.lemma(p.choose_zero_right, &[sm]);
                    let sub_sm0 = d.sub(sm, zero);
                    let h_subzero = d.lemma(p.sub_zero, &[sm]);
                    let rhs = d.choose(sm, sub_sm0);
                    let sm_sm = d.choose(sm, sm);
                    let h_congr = d.congr(sub_sm0, sm, h_subzero, &|d, x| d.choose(sm, x));
                    let h_selfeq = d.lemma(p.choose_self, &[sm]);
                    let (_e, rhs_to_one) = d.chain(rhs, &[(sm_sm, h_congr), (one, h_selfeq)]);
                    let rev = d.symm(rhs, one, rhs_to_one);
                    let body = d.trans(lhs, one, rhs, h_czr, rev);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                &|d, k_prime, _inner_ih| {
                    let sk = d.succ(k_prime);
                    let hyp_ty = d.le(sk, sm);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h2 = d.lemma(p.le_of_succ_le_succ, &[k_prime, m, h]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[k_prime, m, h2]);
                    let strict_ty = d.lt(k_prime, m);
                    let equal_ty = d.eq(k_prime, m);
                    let lhs = d.choose(sm, sk);
                    let subv = d.sub(sm, sk);
                    let rhs = d.choose(sm, subv);
                    let target = d.eq(lhs, rhs);
                    let minor_strict = {
                        let hlt_fv = d.fresh_fvar();
                        let hlt = d.kernel().fvar(hlt_fv);
                        let body = choose_symm_case_lt(d, &p, m, k_prime, h2, hlt, ih);
                        d.lam_fv(hlt_fv, strict_ty, body)
                    };
                    let minor_equal = {
                        let heq_fv = d.fresh_fvar();
                        let heq = d.kernel().fvar(heq_fv);
                        let body = choose_symm_case_eq(d, &p, m, k_prime, heq);
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
                    d.lam_fv(h_fv, hyp_ty, selected)
                },
                k,
            );
            d.lam_fv(k_fv, nat, k_cases)
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt_n);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.choose_symm, ty, value)?;
    Ok(())
}

/// `choose_one_right : ∀ n, choose n 1 = n`, by induction on `n`: the base
/// case is `zero_choose_succ` at `k := 0` (`succ 0 ≡ 1`), and the successor
/// case expands `choose (succ n) 1` via Pascal's rule into `choose n 0 +
/// choose n 1`, closed by `choose_zero_right` and the induction hypothesis
/// plus `add_comm` (the induction hypothesis lands on the right of the sum,
/// where `add`'s right-recursion needs it to collapse `1 + n` to `succ n`).
pub(super) fn declare_choose_one_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.choose_one_right, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let one = d.num(1);
            let lhs = d.choose(x, one);
            d.eq(lhs, x)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.lemma(p.zero_choose_succ, &[zero])
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let zero = d.zero();
                let one = d.num(1);
                let pascal = d.lemma(p.choose_succ_succ, &[j, zero]);
                let cj0 = d.choose(j, zero);
                let cj1 = d.choose(j, one);
                let sum = d.add(cj0, cj1);
                let h_czr = d.lemma(p.choose_zero_right, &[j]);
                let mid = d.add(one, cj1);
                let h1 = d.congr(cj0, one, h_czr, &|d, x| d.add(x, cj1));
                let mid2 = d.add(one, j);
                let h2 = d.congr(cj1, j, ih, &|d, x| d.add(one, x));
                let comm = d.lemma(p.add_comm, &[one, j]);
                let jm1 = d.add(j, one);
                let (_e, sum_to_jm1) = d.chain(sum, &[(mid, h1), (mid2, h2), (jm1, comm)]);
                let target = d.choose(sj, one);
                let step1 = d.trans(target, sum, jm1, pascal, sum_to_jm1);
                let refl_jm1 = d.refl(jm1);
                // `add j one` reduces definitionally to `succ j`, so the
                // stated target `sj` is accepted by defeq without a lemma.
                d.trans(target, jm1, sj, step1, refl_jm1)
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `choose_eq_zero_of_lt : ∀ n k, Lt n k → choose n k = 0`, by induction on
/// `n` with an inner case split on `k` (mirroring [`declare_choose_symm`]'s
/// shape): `n = 0` needs `k`'s shape (`lt_irrefl` refutes `k = 0`;
/// `zero_choose_succ` closes `k = succ k'` directly); `n = succ m` strips one
/// `succ` off both sides of the hypothesis (`le_of_succ_le_succ`,
/// `le_succ_of_le`) to reach two instances of the outer induction hypothesis,
/// combined via [`combine_zero_sum`] and Pascal's rule.
pub(super) fn declare_choose_eq_zero_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hyp = d.lt(n, k);
        let lhs = d.choose(n, k);
        let zero = d.zero();
        let eqn = d.eq(lhs, zero);
        let body = d.arrow(hyp, eqn);
        d.pi_fv(k_fv, nat, body)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_n = stmt_at(d, n);

    let proof = d.induct(
        &stmt_at,
        &|d| {
            // n = 0: fun k (h : Lt 0 k) => choose 0 k = 0
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let inner_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let zero = d.zero();
                let hyp = d.lt(zero, x);
                let lhs = d.choose(zero, x);
                let zero2 = d.zero();
                let eqn = d.eq(lhs, zero2);
                d.arrow(hyp, eqn)
            };
            let k_cases = d.induct(
                &inner_motive,
                &|d| {
                    // fun (h : Lt 0 0) => choose 0 0 = 0 -- vacuous.
                    let zero = d.zero();
                    let hyp_ty = d.lt(zero, zero);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let irrefl = d.lemma(p.lt_irrefl, &[zero]);
                    let false_proof = d.apply(irrefl, &[h]);
                    let goal = {
                        let lhs = d.choose(zero, zero);
                        let zero2 = d.zero();
                        d.eq(lhs, zero2)
                    };
                    let body = absurd(d, goal, false_proof);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                &|d, k_prime, _inner_ih| {
                    // fun (_ : Lt 0 (succ k')) => choose 0 (succ k') = 0
                    let sk = d.succ(k_prime);
                    let zero = d.zero();
                    let hyp_ty = d.lt(zero, sk);
                    let h_fv = d.fresh_fvar();
                    let body = d.lemma(p.zero_choose_succ, &[k_prime]);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                k,
            );
            d.lam_fv(k_fv, nat, k_cases)
        },
        &|d, m, ih| {
            // n = succ m: fun k (h : Lt (succ m) k) => choose (succ m) k = 0
            let sm = d.succ(m);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let inner_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let hyp = d.lt(sm, x);
                let lhs = d.choose(sm, x);
                let zero = d.zero();
                let eqn = d.eq(lhs, zero);
                d.arrow(hyp, eqn)
            };
            let k_cases = d.induct(
                &inner_motive,
                &|d| {
                    // fun (h : Lt (succ m) 0) => choose (succ m) 0 = 0 -- vacuous.
                    let zero = d.zero();
                    let hyp_ty = d.lt(sm, zero);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let not_le = d.lemma(p.not_succ_le_zero, &[sm]);
                    let false_proof = d.apply(not_le, &[h]);
                    let goal = {
                        let lhs = d.choose(sm, zero);
                        let zero2 = d.zero();
                        d.eq(lhs, zero2)
                    };
                    let body = absurd(d, goal, false_proof);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                &|d, k_prime, _inner_ih| {
                    // fun (h : Lt (succ m)(succ k')) => choose (succ m)(succ k') = 0
                    let sk = d.succ(k_prime);
                    let hyp_ty = d.lt(sm, sk);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    // h : Le (succ (succ m)) (succ k')  ≡defeq≡  Lt (succ m) (succ k')
                    let h2 = d.lemma(p.le_of_succ_le_succ, &[sm, k_prime, h]);
                    let ih_k = d.apply(ih, &[k_prime, h2]);
                    let h3 = d.lemma(p.le_succ_of_le, &[sm, k_prime, h2]);
                    let ih_sk = d.apply(ih, &[sk, h3]);
                    let choose_m_kprime = d.choose(m, k_prime);
                    let choose_m_sk = d.choose(m, sk);
                    let combined = combine_zero_sum(d, choose_m_kprime, choose_m_sk, ih_k, ih_sk);
                    let pascal = d.lemma(p.choose_succ_succ, &[m, k_prime]);
                    let target = d.choose(sm, sk);
                    let sum = d.add(choose_m_kprime, choose_m_sk);
                    let zero = d.zero();
                    let final_ = d.trans(target, sum, zero, pascal, combined);
                    d.lam_fv(h_fv, hyp_ty, final_)
                },
                k,
            );
            d.lam_fv(k_fv, nat, k_cases)
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt_n);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.choose_eq_zero_of_lt, ty, value)?;
    Ok(())
}

/// `∀ n k, Le k n → Lt zero (choose n k)`, by induction on `n` with the
/// column `k` case-split (the same shape as
/// [`declare_choose_eq_zero_of_lt`]), used only inside
/// [`declare_choose_ne_zero`] and not exposed as a prelude lemma.
fn choose_pos_all(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hyp = d.le(k, n);
        let zero = d.zero();
        let lhs = d.choose(n, k);
        let lt_ty = d.lt(zero, lhs);
        let body = d.arrow(hyp, lt_ty);
        d.pi_fv(k_fv, nat, body)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let proof = d.induct(
        &stmt_at,
        &|d| {
            // n = 0
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let inner_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let zero = d.zero();
                let hyp = d.le(x, zero);
                let lhs = d.choose(zero, x);
                let zero2 = d.zero();
                let lt_ty = d.lt(zero2, lhs);
                d.arrow(hyp, lt_ty)
            };
            let k_cases = d.induct(
                &inner_motive,
                &|d| {
                    let zero = d.zero();
                    let hyp_ty = d.le(zero, zero);
                    let h_fv = d.fresh_fvar();
                    let body = d.lemma(p.zero_lt_succ, &[zero]);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                &|d, k_prime, _inner_ih| {
                    let sk = d.succ(k_prime);
                    let zero = d.zero();
                    let hyp_ty = d.le(sk, zero);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let not_le = d.lemma(p.not_succ_le_zero, &[k_prime]);
                    let false_proof = d.apply(not_le, &[h]);
                    let goal = {
                        let lhs = d.choose(zero, sk);
                        let zero2 = d.zero();
                        d.lt(zero2, lhs)
                    };
                    let body = absurd(d, goal, false_proof);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                k,
            );
            d.lam_fv(k_fv, nat, k_cases)
        },
        &|d, m, ih| {
            // n = succ m
            let sm = d.succ(m);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let inner_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let hyp = d.le(x, sm);
                let lhs = d.choose(sm, x);
                let zero = d.zero();
                let lt_ty = d.lt(zero, lhs);
                d.arrow(hyp, lt_ty)
            };
            let k_cases = d.induct(
                &inner_motive,
                &|d| {
                    let zero = d.zero();
                    let hyp_ty = d.le(zero, sm);
                    let h_fv = d.fresh_fvar();
                    let body = d.lemma(p.zero_lt_succ, &[zero]);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                &|d, k_prime, _inner_ih| {
                    let sk = d.succ(k_prime);
                    let hyp_ty = d.le(sk, sm);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h2 = d.lemma(p.le_of_succ_le_succ, &[k_prime, m, h]);
                    let pos_left = d.apply(ih, &[k_prime, h2]);
                    let choose_m_kprime = d.choose(m, k_prime);
                    let choose_m_sk = d.choose(m, sk);
                    let base_le = d.lemma(p.le_add_right, &[choose_m_kprime, choose_m_sk]);
                    let zero = d.zero();
                    let sum = d.add(choose_m_kprime, choose_m_sk);
                    let body = d.lemma(
                        p.lt_of_lt_of_le,
                        &[zero, choose_m_kprime, sum, pos_left, base_le],
                    );
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                k,
            );
            d.lam_fv(k_fv, nat, k_cases)
        },
        n,
    );

    d.lam_fv(n_fv, nat, proof)
}

/// `choose_ne_zero : ∀ n k, Le k n → choose n k ≠ 0`, via [`choose_pos_all`]
/// (`0 < choose n k`) transported along a hypothetical `choose n k = 0` into
/// `0 < 0`, refuted by `lt_irrefl`.
pub(super) fn declare_choose_ne_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let pos_all = choose_pos_all(d, &p);
    d.theorem(p.choose_ne_zero, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let hyp = d.le(k, n);
        let cnk = d.choose(n, k);
        let zero = d.zero();
        let eqn = d.eq(cnk, zero);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let ne_ty = d.arrow(eqn, false_ty);
        let stmt = d.arrow(hyp, ne_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let pos = d.apply(pos_all, &[n, k, h]);
        let motive_lt = d.eq_motive(cnk, &|d, x| {
            let zero = d.zero();
            d.lt(zero, x)
        });
        let lt_zero_zero = d.transport(cnk, motive_lt, pos, zero, heq);
        let irrefl = d.lemma(p.lt_irrefl, &[zero]);
        let contradiction = d.apply(irrefl, &[lt_zero_zero]);

        let inner = d.lam_fv(heq_fv, eqn, contradiction);
        let outer = d.lam_fv(h_fv, hyp, inner);
        (stmt, outer)
    })?;
    Ok(())
}

/// `choose_le_succ : ∀ a c, choose a c ≤ choose (succ a) c`, by induction on
/// `c`: `c = 0` has both sides defeq `1` (`le_refl`); `c = succ c'` expands
/// the successor side via Pascal's rule into `choose a c' + choose a c`,
/// which dominates `choose a c` by `le_add_right` plus `add_comm` (Pascal's
/// natural order puts `choose a c` second in the sum).
pub(super) fn declare_choose_le_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.choose_le_succ, 2, &|d, v| {
        let (a, c) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let ca = d.choose(a, x);
            let sa = d.succ(a);
            let csa = d.choose(sa, x);
            d.le(ca, csa)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                // `choose a 0` is stuck on symbolic `a` (the outer recursor
                // needs a constructor-shaped first argument), so this needs
                // `choose_zero_right`, not defeq -- unlike `choose (succ a) 0`,
                // which reduces to `1` regardless of `a`.
                let zero = d.zero();
                let ca0 = d.choose(a, zero);
                let one = d.num(1);
                let h_czr = d.lemma(p.choose_zero_right, &[a]);
                let base = d.lemma(p.le_refl, &[one]);
                let motive2 = d.eq_motive(one, &|d, x| d.le(x, one));
                let sym = d.symm(ca0, one, h_czr);
                d.transport(one, motive2, base, ca0, sym)
            },
            &|d, cprime, _ih| {
                let ca_cprime = d.choose(a, cprime);
                let sc = d.succ(cprime);
                let ca_c = d.choose(a, sc);
                let base = d.lemma(p.le_add_right, &[ca_c, ca_cprime]);
                let comm = d.lemma(p.add_comm, &[ca_c, ca_cprime]);
                let sum1 = d.add(ca_c, ca_cprime);
                let sum2 = d.add(ca_cprime, ca_c);
                let motive2 = d.eq_motive(sum1, &|d, x| d.le(ca_c, x));
                d.transport(sum1, motive2, base, sum2, comm)
            },
            c,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `choose_symm_of_eq_add : ∀ n a b, n = a + b → choose n a = choose n b` —
/// [`declare_choose_symm`] restated at the additive witness: `a ≤ a+b`
/// (`le_add_right`) supplies `choose_symm`'s hypothesis (transported along
/// `n = a+b`), and `add_sub_cancel_left` rewrites its `n - a` conclusion to
/// `b`.
pub(super) fn declare_choose_symm_of_eq_add(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.choose_symm_of_eq_add, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let sum_ab = d.add(a, b);
        let heq_ty = d.eq(n, sum_ab);
        let choose_na = d.choose(n, a);
        let choose_nb = d.choose(n, b);
        let concl = d.eq(choose_na, choose_nb);
        let stmt = d.arrow(heq_ty, concl);

        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        // Le a n, from `le_add_right a b : Le a (add a b)` transported along
        // `n = a+b`.
        let base_le = d.lemma(p.le_add_right, &[a, b]);
        let motive_le = d.eq_motive(sum_ab, &|d, x| d.le(a, x));
        let sym_heq = d.symm(n, sum_ab, heq);
        let h_le = d.transport(sum_ab, motive_le, base_le, n, sym_heq);

        // choose n a = choose n (n - a), via choose_symm.
        let symm_step = d.lemma(p.choose_symm, &[n, a, h_le]);
        let sub_na = d.sub(n, a);
        let choose_n_sub_na = d.choose(n, sub_na);

        // n - a = b: rewrite `n` to `a+b` inside `sub(_, a)`, then
        // `add_sub_cancel_left`.
        let cancel = d.lemma(p.add_sub_cancel_left, &[a, b]);
        let sub_sum_ab = d.sub(sum_ab, a);
        let h_congr_sub = d.congr(n, sum_ab, heq, &|d, x| d.sub(x, a));
        let sub_na_eq_b = d.trans(sub_na, sub_sum_ab, b, h_congr_sub, cancel);

        // choose n (n-a) = choose n b.
        let h_congr_choose = d.congr(sub_na, b, sub_na_eq_b, &|d, x| d.choose(n, x));

        let final_ = d.trans(
            choose_na,
            choose_n_sub_na,
            choose_nb,
            symm_step,
            h_congr_choose,
        );
        let body = d.lam_fv(heq_fv, heq_ty, final_);
        (stmt, body)
    })?;
    Ok(())
}

/// `choose_le_add : ∀ a b c, choose a c ≤ choose (a + b) c`, by induction on
/// `b`: `b = 0` has `add a zero ≡ a` definitionally, so both sides are the
/// same `choose a c` (`le_refl`); `b = succ b'` has `add a (succ b') ≡ succ
/// (add a b')` definitionally, so the goal is `Le (choose a c) (choose (succ
/// (add a b')) c)`, closed by chaining the induction hypothesis with
/// `choose_le_succ (add a b') c` through `le_trans`.
pub(super) fn declare_choose_le_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.choose_le_add, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let ca = d.choose(a, c);
            let ax = d.add(a, x);
            let cax = d.choose(ax, c);
            d.le(ca, cax)
        };
        let stmt = motive(d, b);
        let proof = d.induct(
            &motive,
            &|d| {
                let ca = d.choose(a, c);
                d.const_app(p.le_refl, &[ca])
            },
            &|d, bprime, ih| {
                let ca = d.choose(a, c);
                let ab = d.add(a, bprime);
                let choose_ab_c = d.choose(ab, c);
                let succ_ab = d.succ(ab);
                let choose_succ_ab_c = d.choose(succ_ab, c);
                let step = d.lemma(p.choose_le_succ, &[ab, c]);
                d.lemma(p.le_trans, &[ca, choose_ab_c, choose_succ_ab_c, ih, step])
            },
            b,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `choose_symm_add : ∀ a b, choose (a + b) a = choose (a + b) b` —
/// [`declare_choose_symm_of_eq_add`] instantiated at `n := a + b` with its
/// hypothesis closed by `refl`, since `n = a + b` is then the identity.
pub(super) fn declare_choose_symm_add(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.choose_symm_add, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let n = d.add(a, b);
        let refl_n = d.refl(n);
        let proof = d.lemma(p.choose_symm_of_eq_add, &[n, a, b, refl_n]);
        let choose_na = d.choose(n, a);
        let choose_nb = d.choose(n, b);
        let stmt = d.eq(choose_na, choose_nb);
        (stmt, proof)
    })?;
    Ok(())
}

/// `choose_le_choose : ∀ a b c, Le a b → Le (choose a c) (choose b c)`.
///
/// Route: `d0 := sub b a`; `sub_add_cancel(a, b, h) : Eq (add d0 a) b`;
/// flip the addend order with `add_comm(d0, a)` (via `symm`/`trans`) to get
/// `Eq (add a d0) b`; `choose_le_add(a, d0, c) : Le (choose a c) (choose
/// (add a d0) c)` then transports along that equation to the goal.
pub(super) fn declare_choose_le_choose(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.choose_le_choose, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let le_ty = d.le(a, b);
        let stmt = {
            let ca = d.choose(a, c);
            let cb = d.choose(b, c);
            let concl = d.le(ca, cb);
            d.arrow(le_ty, concl)
        };

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let d0 = d.sub(b, a);
        let add_d0_a = d.add(d0, a);
        let add_a_d0 = d.add(a, d0);
        let cancel = d.lemma(p.sub_add_cancel, &[a, b, h]);
        let comm = d.lemma(p.add_comm, &[d0, a]);
        let comm_flip = d.symm(add_d0_a, add_a_d0, comm);
        let combined = d.trans(add_a_d0, add_d0_a, b, comm_flip, cancel);

        let step = d.lemma(p.choose_le_add, &[a, d0, c]);

        let ca = d.choose(a, c);
        let motive = d.eq_motive(add_a_d0, &|d, x| {
            let cx = d.choose(x, c);
            d.le(ca, cx)
        });
        let result = d.transport(add_a_d0, motive, step, b, combined);

        let body = d.lam_fv(h_fv, le_ty, result);
        (stmt, body)
    })?;
    Ok(())
}

/// `choose_mono : ∀ c a a', Le a a' → Le (choose a c) (choose a' c)` — the
/// core-rendered unfolding of Mathlib's `Nat.choose_mono : ∀ b, Monotone (fun
/// a => a.choose b)`. `Monotone f` unfolds to `∀ x y, x ≤ y → f x ≤ f y`, so
/// with `f := fun a => choose a c` this is exactly [`declare_choose_le_choose`]
/// with its arguments permuted so the fixed column `c` comes first: apply
/// `choose_le_choose(a, a', c, h)` directly, no new induction needed.
pub(super) fn declare_choose_mono(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.choose_mono, 1, &|d, v| {
        let c = v[0];

        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let ap_fv = d.fresh_fvar();
        let ap = d.kernel().fvar(ap_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let nat = d.nat_ty();
        let le_ty = d.le(a, ap);
        let ca = d.choose(a, c);
        let cap = d.choose(ap, c);
        let concl = d.le(ca, cap);
        let inner_ty = d.arrow(le_ty, concl);
        let stmt = {
            let out = d.pi_fv(ap_fv, nat, inner_ty);
            d.pi_fv(a_fv, nat, out)
        };

        let body = d.lemma(p.choose_le_choose, &[a, ap, c, h]);
        let inner_proof = d.lam_fv(h_fv, le_ty, body);
        let proof = {
            let out = d.lam_fv(ap_fv, nat, inner_proof);
            d.lam_fv(a_fv, nat, out)
        };
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `choose` and every theorem in this module, in dependency order.
pub(super) fn declare_choose_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_choose(d, p)?;
    declare_choose_equations(d, p)?;
    declare_choose_self(d, p)?;
    declare_choose_symm(d, p)?;
    declare_choose_one_right(d, p)?;
    declare_choose_eq_zero_of_lt(d, p)?;
    declare_choose_ne_zero(d, p)?;
    declare_choose_le_succ(d, p)?;
    declare_choose_symm_of_eq_add(d, p)?;
    declare_choose_le_add(d, p)?;
    declare_choose_symm_add(d, p)?;
    declare_choose_le_choose(d, p)?;
    declare_choose_mono(d, p)?;
    Ok(())
}
