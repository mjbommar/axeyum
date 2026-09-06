//! `Nat.Multiset.prodSel` — the product of a multiset restricted by a
//! `Nat → Bool` predicate, and the half of the divisors ↔ subsets bijection
//! that unique factorization already pays for (roadmap W2-18, ADR-1658).
//!
//! # What ADR-1624 asked for, and what a multiset here actually is
//!
//! ADR-1624 named the blocker under Möbius inversion as "a multiset indexed by
//! a `Nat → Bool` predicate", and described the wanted object as a product over
//! the *selected positions of the multiset's list representation*. **There is no
//! list.** `Nat.Multiset` (`multiset.rs`) is a multiplicity function
//! `Nat → Nat` together with a bound, and `count` truncates at the bound; order
//! is never represented, so "position `i`" does not name anything.
//!
//! The index set that *is* available is the VALUE: `Nat.Multiset.prod` folds
//! `prodRange (fun q => q ^ count m q) (bound m)`, i.e. over `q ∈ [0, bound m)`,
//! and a subset of `[0, n)` in this prelude is exactly a `Nat → Bool`
//! (`Nat.Subsets.empty`/`insertAt`, `subset_sums.rs`). So the selection is by
//! value and the two index spaces already agree:
//!
//! ```text
//! Nat.Multiset.prodSel m s := prodRange (fun q => if s q then q ^ count m q
//!                                                 else 1) (bound m)
//! ```
//!
//! This is a deliberate deviation from ADR-1624's wording, recorded in
//! ADR-1658. It is the same object for the intended consumer — for squarefree
//! `n` every `count` is `0` or `1`, so a selection of values IS a selection of
//! prime factors — and it costs no enumeration of the support.
//!
//! # `restrict` is what makes the hard half free
//!
//! The selection could stop at the fold above, and then every fact about it
//! would be a fresh induction over `prodRange`. Instead the fold is tied to a
//! multiset:
//!
//! ```text
//! Nat.Multiset.restrict m s := mk (fun q => if s q then raw m q else 0)
//!                                 (bound m)
//! ```
//!
//! — the SAME bound, so `Nat.Multiset.count_restrict` is unconditional
//! (`count (restrict m s) q = if s q then count m q else 0`, with no `q < bound`
//! side condition), and `Nat.Multiset.prodSel_eq_prod_restrict` says the fold IS
//! a multiset product. That one theorem is what turns
//! `Nat.Multiset.count_eq_of_prod_eq` — uniqueness of prime factorization,
//! already proved in `multiset.rs` — into `Nat.Multiset.prodSel_injective` with
//! no new arithmetic at all: two selections with the same product agree at
//! every value the multiset actually contains.
//!
//! `restrict` is defined through `raw`, not through `count`. Through `count` the
//! statement of `count_restrict` would be true but its proof would need a
//! `q < bound m` case split; through `raw` both sides of `count_restrict` are
//! two nested `Bool.rec`s over the same two conditions in the opposite order,
//! and the whole proof is one `Bool.rec` on `s q` whose `false` branch is
//! `Nat.bool_select_nat_same` and whose `true` branch is `Eq.refl`.
//!
//! # What is here, and what is NOT
//!
//! Landed:
//!
//! - `Nat.mul_dvd_mul` and `Nat.prodRange_dvd_prodRange` — general, neither
//!   mentions `Nat.Multiset`. The prelude had `Nat.dvd_mul`,
//!   `Nat.dvd_mul_right_of_dvd` and `Nat.dvd_trans` but nothing multiplying two
//!   divisibilities, and hence no way to push a pointwise divisibility under a
//!   product fold.
//! - `Nat.bool_select_nat_inj_of_pos` — a `{c, 0}` select is injective in its
//!   CONDITION when `c > 0`. This is the step that reads a `Bool` back out of an
//!   arithmetic identity, and the positivity is load-bearing: at `c = 0` both
//!   selects are `0` and the conclusion is false.
//! - `Nat.Multiset.restrict`, `Nat.Multiset.prodSel`, and the laws
//!   `bound_restrict`/`count_restrict`/`count_restrict_pos`/
//!   `prodSel_eq_prod_restrict`/`prodSel_all`/`prodSel_empty`/`prodSel_congr`/
//!   `prodSel_dvd_prod`/`prodSel_injective`.
//!
//! NOT here, and sized in ADR-1658: the other half of the bijection — every
//! divisor of a squarefree `n` IS a `prodSel` — and the transfer of
//! `sumRangeIf (· ∣ n) f (n+1)` to `sumSubsets (bound m) (fun s => f (prodSel m
//! s))`. `prodSel_dvd_prod` gives the easy direction (every selection is a
//! divisor) and `prodSel_injective` gives injectivity; what is missing is
//! surjectivity onto the divisors and, separately, a sum-transfer law between
//! two DIFFERENT index shapes (a `Nat` range and a `Nat → Bool` fold). This
//! prelude's `Nat.countRange_bij` is the cross-bound law for COUNTS over two
//! `Nat` ranges; there is no `sumRange` twin and no range-to-subset twin.
//!
//! # House rules observed here
//!
//! Every helper hoists each sub-expression into its own `let` before passing it
//! to a `NatOps` method (`&mut NatDev` cannot be reborrowed twice in one call),
//! as `multiset.rs` and `multiset_prod.rs` document. Every numeral the tests
//! build is tiny: this prelude's numerals are unary `succ` towers and cost is
//! superlinear in the largest magnitude FORMED.

#![allow(clippy::too_many_lines)]

use super::NatPrelude;
use super::multiset::{mk_multiset, ms_bound, ms_count, ms_prod, ms_raw, prod_range};
use super::ops::{NatDev, NatOps, bool_select_nat_same};
use super::primes::prime_condition;
use super::steps::{absurd, dvd_elim, dvd_intro};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::{BinderInfo, ExprId};
use crate::name::NameId;

/// Delta height for `Nat.Multiset.restrict`: above `raw`/`bound` (1) and
/// `count` (2), which it does not call but is always reduced underneath it.
const RESTRICT_HEIGHT: u16 = 3;
/// Delta height for `Nat.Multiset.prodSel`: above `Nat.prodRange` (2),
/// `Nat.Multiset.prod` (3) and `Nat.Multiset.restrict` (3), so a defeq check
/// against either unfolds `prodSel` first.
const PROD_SEL_HEIGHT: u16 = 4;

// ---------------------------------------------------------------------------
// Term builders.
// ---------------------------------------------------------------------------

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

/// `Nat.Multiset`.
fn multiset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.multiset, vec![])
}

/// `Nat → Bool` — a selection, as a decidable membership predicate. The same
/// carrier `Nat.Subsets` uses (`subset_sums.rs`).
fn set_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    d.arrow(nat, bool_ty)
}

/// `Nat.Multiset.restrict m s`.
fn ms_restrict(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, s: ExprId) -> ExprId {
    d.const_app(p.multiset_restrict, &[m, s])
}

/// `Nat.Multiset.prodSel m s`.
fn ms_prod_sel(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, s: ExprId) -> ExprId {
    d.const_app(p.multiset_prod_sel, &[m, s])
}

/// `fun q => if s q then pow q (count m q) else 1` — the factor `prodSel`
/// folds.
fn select_factor(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, s: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let c = ms_count(d, &p, m, q);
    let powered = d.pow(q, c);
    let one = d.num(1);
    let sq = d.apply(s, &[q]);
    let body = d.bool_select_nat(sq, powered, one);
    d.lam_fv(q_fv, nat, body)
}

/// `fun q => pow q (count m q)` — the factor `Nat.Multiset.prod` folds, at an
/// arbitrary multiset expression.
fn count_pow_factor(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let c = ms_count(d, &p, m, q);
    let body = d.pow(q, c);
    d.lam_fv(q_fv, nat, body)
}

/// `Bool.rec` at a `Prop` motive: case analysis on `b`, with the branch proofs
/// built by the two closures.
fn bool_cases(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    b: ExprId,
    motive: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    at_false: &dyn Fn(&mut NatDev<'_>) -> ExprId,
    at_true: &dyn Fn(&mut NatDev<'_>) -> ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let motive_lam = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = motive(d, x);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let false_case = at_false(d);
    let true_case = at_true(d);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(rec, &[motive_lam, false_case, true_case, b])
}

/// `(a·u)·(c·v) = (a·c)·(u·v)` — the four-factor rearrangement, three
/// `mul_assoc`s and one `mul_comm`, the same shape `Nat.prodRange_mul`'s
/// successor step uses (`multiset_prod.rs`).
fn mul_four_swap(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    u: ExprId,
    c: ExprId,
    v: ExprId,
) -> ExprId {
    let p = *p;
    let au = d.mul(a, u);
    let cv = d.mul(c, v);
    let start = d.mul(au, cv);

    // (a·u)·(c·v) = a·(u·(c·v))
    let u_cv = d.mul(u, cv);
    let s1_to = d.mul(a, u_cv);
    let s1 = d.lemma(p.mul_assoc, &[a, u, cv]);

    // u·(c·v) = (u·c)·v
    let uc = d.mul(u, c);
    let uc_v = d.mul(uc, v);
    let assoc_ucv = d.lemma(p.mul_assoc, &[u, c, v]);
    let inner2 = d.symm(uc_v, u_cv, assoc_ucv);
    let s2_to = d.mul(a, uc_v);
    let s2 = d.congr(u_cv, uc_v, inner2, &|d, y| d.mul(a, y));

    // (u·c)·v = (c·u)·v
    let cu = d.mul(c, u);
    let comm = d.lemma(p.mul_comm, &[u, c]);
    let cu_v = d.mul(cu, v);
    let inner3 = d.congr(uc, cu, comm, &|d, y| d.mul(y, v));
    let s3_to = d.mul(a, cu_v);
    let s3 = d.congr(uc_v, cu_v, inner3, &|d, y| d.mul(a, y));

    // (c·u)·v = c·(u·v)
    let uv = d.mul(u, v);
    let c_uv = d.mul(c, uv);
    let inner4 = d.lemma(p.mul_assoc, &[c, u, v]);
    let s4_to = d.mul(a, c_uv);
    let s4 = d.congr(cu_v, c_uv, inner4, &|d, y| d.mul(a, y));

    // a·(c·(u·v)) = (a·c)·(u·v)
    let ac = d.mul(a, c);
    let end = d.mul(ac, uv);
    let assoc_final = d.lemma(p.mul_assoc, &[a, c, uv]);
    let s5 = d.symm(end, s4_to, assoc_final);

    let (_, proof) = d.chain(
        start,
        &[
            (s1_to, s1),
            (s2_to, s2),
            (s3_to, s3),
            (s4_to, s4),
            (end, s5),
        ],
    );
    proof
}

// ---------------------------------------------------------------------------
// The three general laws. None of them mentions `Nat.Multiset`.
// ---------------------------------------------------------------------------

fn declare_dvd_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // mul_dvd_mul : ∀ a b c e, dvd a b → dvd c e → dvd (mul a c) (mul b e)
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        let hab_ty = d.dvd(a, b);
        let hce_ty = d.dvd(c, e);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);
        let hce_fv = d.fresh_fvar();
        let hce = d.kernel().fvar(hce_fv);

        let ac = d.mul(a, c);
        let be = d.mul(b, e);
        let goal = d.dvd(ac, be);

        let proof = dvd_elim(d, a, b, goal, hab, &|d, u, hb| {
            // hb : Eq b (mul a u)
            dvd_elim(d, c, e, goal, hce, &|d, v, he| {
                // he : Eq e (mul c v)
                let au = d.mul(a, u);
                let cv = d.mul(c, v);
                let uv = d.mul(u, v);
                let ac_inner = d.mul(a, c);
                let be_inner = d.mul(b, e);

                // b·e = (a·u)·e
                let step1_to = d.mul(au, e);
                let step1 = d.congr(b, au, hb, &|d, y| d.mul(y, e));
                // (a·u)·e = (a·u)·(c·v)
                let step2_to = d.mul(au, cv);
                let step2 = d.congr(e, cv, he, &|d, y| d.mul(au, y));
                // (a·u)·(c·v) = (a·c)·(u·v)
                let step3_to = d.mul(ac_inner, uv);
                let step3 = mul_four_swap(d, &p, a, u, c, v);

                let (_, eq_proof) = d.chain(
                    be_inner,
                    &[(step1_to, step1), (step2_to, step2), (step3_to, step3)],
                );
                dvd_intro(d, ac_inner, be_inner, uv, eq_proof)
            })
        });

        declare_forall(
            d,
            p.mul_dvd_mul,
            &[
                (a_fv, nat),
                (b_fv, nat),
                (c_fv, nat),
                (e_fv, nat),
                (hab_fv, hab_ty),
                (hce_fv, hce_ty),
            ],
            goal,
            proof,
        )?;
    }

    // prodRange_dvd_prodRange : ∀ f g n, (∀ i, dvd (f i) (g i)) →
    //   dvd (prodRange f n) (prodRange g n)
    {
        let fn_ty = d.arrow(nat, nat);
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
            let body = d.dvd(fi, gi);
            d.pi_fv(i_fv, nat, body)
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let claim = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
            let lhs = prod_range(d, &p, f, k);
            let rhs = prod_range(d, &p, g, k);
            d.dvd(lhs, rhs)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            // Both folds reduce to `1`; `dvd 1 1` is `dvd_refl 1`.
            let one = d.num(1);
            d.lemma(p.dvd_refl, &[one])
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let pf = prod_range(d, &p, f, j);
            let pg = prod_range(d, &p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let hj = d.apply(h, &[j]);
            d.lemma(p.mul_dvd_mul, &[pf, pg, fj, gj, ih, hj])
        };
        let proof = d.induct(&claim, &base, &step, n);
        let stmt = claim(d, n);
        declare_forall(
            d,
            p.prod_range_dvd_prod_range,
            &[(f_fv, fn_ty), (g_fv, fn_ty), (n_fv, nat), (h_fv, hyp_ty)],
            stmt,
            proof,
        )?;
    }

    // bool_select_nat_inj_of_pos : ∀ c, Lt zero c → ∀ (b1 b2 : Bool),
    //   Eq Nat (if b1 then c else 0) (if b2 then c else 0) → Eq Bool b1 b2
    {
        let bool_ty = d.bool_ty();
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let zero = d.zero();
        let hc_ty = d.lt(zero, c);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let b1_fv = d.fresh_fvar();
        let b1 = d.kernel().fvar(b1_fv);
        let b2_fv = d.fresh_fvar();
        let b2 = d.kernel().fvar(b2_fv);

        let hyp_ty = {
            let z1 = d.zero();
            let lhs = d.bool_select_nat(b1, c, z1);
            let z2 = d.zero();
            let rhs = d.bool_select_nat(b2, c, z2);
            d.eq(lhs, rhs)
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let goal = d.bool_eq(b1, b2);

        // `Eq c zero` contradicts `Lt zero c`.
        let from_c_eq_zero = |d: &mut NatDev<'_>, target: ExprId, h_c_zero: ExprId| -> ExprId {
            let z = d.zero();
            let motive = d.eq_motive(c, &|d, x| {
                let z_inner = d.zero();
                d.lt(z_inner, x)
            });
            let lt_zero_zero = d.transport(c, motive, hc, z, h_c_zero);
            let not_lt = d.lemma(p.not_lt_zero, &[z]);
            let contradiction = d.apply(not_lt, &[lt_zero_zero]);
            absurd(d, target, contradiction)
        };

        let outer = bool_cases(
            d,
            &p,
            b1,
            &|d, x| {
                let z1 = d.zero();
                let lhs = d.bool_select_nat(x, c, z1);
                let z2 = d.zero();
                let rhs = d.bool_select_nat(b2, c, z2);
                let hyp = d.eq(lhs, rhs);
                let concl = d.bool_eq(x, b2);
                d.arrow(hyp, concl)
            },
            // b1 = false: `Eq zero (if b2 then c else 0) → Eq Bool false b2`.
            &|d| {
                bool_cases(
                    d,
                    &p,
                    b2,
                    &|d, y| {
                        let z = d.zero();
                        let z_inner = d.zero();
                        let rhs = d.bool_select_nat(y, c, z_inner);
                        let hyp = d.eq(z, rhs);
                        let f_inner = d.bool_false();
                        let concl = d.bool_eq(f_inner, y);
                        d.arrow(hyp, concl)
                    },
                    // b2 = false: `Eq 0 0 → Eq Bool false false`.
                    &|d| {
                        let z1 = d.zero();
                        let z2 = d.zero();
                        let hyp = d.eq(z1, z2);
                        let f_inner = d.bool_false();
                        let body = d.bool_refl(f_inner);
                        let anon = d.anon_name();
                        d.kernel().lam(anon, hyp, body, BinderInfo::Default)
                    },
                    // b2 = true: `Eq 0 c → Eq Bool false true`, impossible.
                    &|d| {
                        let z = d.zero();
                        let hyp = d.eq(z, c);
                        let hfv = d.fresh_fvar();
                        let hh = d.kernel().fvar(hfv);
                        let f_inner = d.bool_false();
                        let t_inner = d.bool_true();
                        let target = d.bool_eq(f_inner, t_inner);
                        let z_again = d.zero();
                        let flipped = d.symm(z_again, c, hh);
                        let body = from_c_eq_zero(d, target, flipped);
                        d.lam_fv(hfv, hyp, body)
                    },
                )
            },
            // b1 = true: `Eq c (if b2 then c else 0) → Eq Bool true b2`.
            &|d| {
                bool_cases(
                    d,
                    &p,
                    b2,
                    &|d, y| {
                        let z_inner = d.zero();
                        let rhs = d.bool_select_nat(y, c, z_inner);
                        let hyp = d.eq(c, rhs);
                        let t_inner = d.bool_true();
                        let concl = d.bool_eq(t_inner, y);
                        d.arrow(hyp, concl)
                    },
                    // b2 = false: `Eq c 0 → Eq Bool true false`, impossible.
                    &|d| {
                        let z = d.zero();
                        let hyp = d.eq(c, z);
                        let hfv = d.fresh_fvar();
                        let hh = d.kernel().fvar(hfv);
                        let t_inner = d.bool_true();
                        let f_inner = d.bool_false();
                        let target = d.bool_eq(t_inner, f_inner);
                        let body = from_c_eq_zero(d, target, hh);
                        d.lam_fv(hfv, hyp, body)
                    },
                    // b2 = true: `Eq c c → Eq Bool true true`.
                    &|d| {
                        let hyp = d.eq(c, c);
                        let t_inner = d.bool_true();
                        let body = d.bool_refl(t_inner);
                        let anon = d.anon_name();
                        d.kernel().lam(anon, hyp, body, BinderInfo::Default)
                    },
                )
            },
        );
        let proof = d.apply(outer, &[h]);

        declare_forall(
            d,
            p.bool_select_nat_inj_of_pos,
            &[
                (c_fv, nat),
                (hc_fv, hc_ty),
                (b1_fv, bool_ty),
                (b2_fv, bool_ty),
                (h_fv, hyp_ty),
            ],
            goal,
            proof,
        )?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// `Nat.Multiset.restrict` and `Nat.Multiset.prodSel`.
// ---------------------------------------------------------------------------

fn declare_definitions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let ms = multiset_ty(d, &p);
    let sty = set_ty(d);

    // restrict : Multiset → (Nat → Bool) → Multiset
    //   := fun m s => mk (fun q => if s q then raw m q else 0) (bound m)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let f = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let raw_m = ms_raw(d, &p, m);
            let raw_at = d.apply(raw_m, &[q]);
            let zero = d.zero();
            let sq = d.apply(s, &[q]);
            let body = d.bool_select_nat(sq, raw_at, zero);
            d.lam_fv(q_fv, nat, body)
        };
        let b = ms_bound(d, &p, m);
        let built = mk_multiset(d, &p, f, b);
        let value = {
            let inner = d.lam_fv(s_fv, sty, built);
            d.lam_fv(m_fv, ms, inner)
        };
        let ty = {
            let inner = d.arrow(sty, ms);
            d.arrow(ms, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_restrict,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(RESTRICT_HEIGHT),
        })?;
    }

    // prodSel : Multiset → (Nat → Bool) → Nat
    //   := fun m s => prodRange (fun q => if s q then pow q (count m q) else 1)
    //                           (bound m)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let f = select_factor(d, &p, m, s);
        let b = ms_bound(d, &p, m);
        let body = prod_range(d, &p, f, b);
        let value = {
            let inner = d.lam_fv(s_fv, sty, body);
            d.lam_fv(m_fv, ms, inner)
        };
        let ty = {
            let inner = d.arrow(sty, nat);
            d.arrow(ms, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_prod_sel,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(PROD_SEL_HEIGHT),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The laws.
// ---------------------------------------------------------------------------

fn declare_restrict_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let ms = multiset_ty(d, &p);
    let sty = set_ty(d);

    // bound_restrict : ∀ m s, Eq (bound (restrict m s)) (bound m) — refl.
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let r = ms_restrict(d, &p, m, s);
        let lhs = ms_bound(d, &p, r);
        let rhs = ms_bound(d, &p, m);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        declare_forall(
            d,
            p.multiset_bound_restrict,
            &[(m_fv, ms), (s_fv, sty)],
            stmt,
            proof,
        )?;
    }

    // count_restrict : ∀ m s q,
    //   Eq (count (restrict m s) q) (if s q then count m q else 0)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);

        let r = ms_restrict(d, &p, m, s);
        let lhs = ms_count(d, &p, r, q);
        let cm = ms_count(d, &p, m, q);
        let zero = d.zero();
        let sq = d.apply(s, &[q]);
        let rhs = d.bool_select_nat(sq, cm, zero);
        let stmt = d.eq(lhs, rhs);

        // Both sides unfold to two nested selects over `cond := ble (succ q)
        // (bound m)` and `s q`, in opposite orders, over `raw m q`.
        let cond = {
            let succ_q = d.succ(q);
            let b = ms_bound(d, &p, m);
            d.ble(succ_q, b)
        };
        let raw_at = {
            let raw_m = ms_raw(d, &p, m);
            d.apply(raw_m, &[q])
        };
        let proof = bool_cases(
            d,
            &p,
            sq,
            &|d, x| {
                let z1 = d.zero();
                let inner_l = d.bool_select_nat(x, raw_at, z1);
                let z2 = d.zero();
                let left = d.bool_select_nat(cond, inner_l, z2);
                let z3 = d.zero();
                let inner_r = d.bool_select_nat(cond, raw_at, z3);
                let z4 = d.zero();
                let right = d.bool_select_nat(x, inner_r, z4);
                d.eq(left, right)
            },
            // s q = false: `if cond then 0 else 0 = 0`.
            &|d| {
                let z = d.zero();
                bool_select_nat_same(d, &p, cond, z)
            },
            // s q = true: both sides are `if cond then raw m q else 0`.
            &|d| {
                let z = d.zero();
                let both = d.bool_select_nat(cond, raw_at, z);
                d.refl(both)
            },
        );
        declare_forall(
            d,
            p.multiset_count_restrict,
            &[(m_fv, ms), (s_fv, sty), (q_fv, nat)],
            stmt,
            proof,
        )?;
    }

    // count_restrict_pos : ∀ m s q, Lt 0 (count (restrict m s) q) →
    //   Lt 0 (count m q)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);

        let r = ms_restrict(d, &p, m, s);
        let cr = ms_count(d, &p, r, q);
        let zero = d.zero();
        let hyp_ty = d.lt(zero, cr);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let cm = ms_count(d, &p, m, q);
        let goal = {
            let z = d.zero();
            d.lt(z, cm)
        };

        // Move the hypothesis across `count_restrict`, then case on `s q`.
        let sq = d.apply(s, &[q]);
        let hcr = d.lemma(p.multiset_count_restrict, &[m, s, q]);
        let sel = {
            let z = d.zero();
            d.bool_select_nat(sq, cm, z)
        };
        let moved = {
            let motive = d.eq_motive(cr, &|d, x| {
                let z = d.zero();
                d.lt(z, x)
            });
            d.transport(cr, motive, h, sel, hcr)
        };
        let cases = bool_cases(
            d,
            &p,
            sq,
            &|d, x| {
                let z1 = d.zero();
                let inner = d.bool_select_nat(x, cm, z1);
                let z2 = d.zero();
                let hyp = d.lt(z2, inner);
                let z3 = d.zero();
                let concl = d.lt(z3, cm);
                d.arrow(hyp, concl)
            },
            // s q = false: `Lt 0 0` is impossible.
            &|d| {
                let z = d.zero();
                let z2 = d.zero();
                let hyp = d.lt(z, z2);
                let hfv = d.fresh_fvar();
                let hh = d.kernel().fvar(hfv);
                let z3 = d.zero();
                let not_lt = d.lemma(p.not_lt_zero, &[z3]);
                let contradiction = d.apply(not_lt, &[hh]);
                let target = {
                    let z_inner = d.zero();
                    d.lt(z_inner, cm)
                };
                let body = absurd(d, target, contradiction);
                d.lam_fv(hfv, hyp, body)
            },
            // s q = true: the hypothesis IS the goal.
            &|d| {
                let z = d.zero();
                let hyp = d.lt(z, cm);
                let hfv = d.fresh_fvar();
                let hh = d.kernel().fvar(hfv);
                d.lam_fv(hfv, hyp, hh)
            },
        );
        let proof = d.apply(cases, &[moved]);

        declare_forall(
            d,
            p.multiset_count_restrict_pos,
            &[(m_fv, ms), (s_fv, sty), (q_fv, nat), (h_fv, hyp_ty)],
            goal,
            proof,
        )?;
    }

    Ok(())
}

fn declare_prod_sel_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let ms = multiset_ty(d, &p);
    let sty = set_ty(d);

    // prodSel_eq_prod_restrict : ∀ m s, Eq (prodSel m s) (prod (restrict m s))
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);

        let r = ms_restrict(d, &p, m, s);
        let lhs = ms_prod_sel(d, &p, m, s);
        let rhs = ms_prod(d, &p, r);
        let stmt = d.eq(lhs, rhs);

        let f = select_factor(d, &p, m, s);
        let g = count_pow_factor(d, &p, r);
        let b = ms_bound(d, &p, m);
        let pointwise = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let cm = ms_count(d, &p, m, q);
            let cr = ms_count(d, &p, r, q);
            let sq = d.apply(s, &[q]);
            let zero = d.zero();
            let sel_count = d.bool_select_nat(sq, cm, zero);
            let powered = d.pow(q, cm);
            let one = d.num(1);
            let start = d.bool_select_nat(sq, powered, one);

            // if s q then q^count m q else 1 = q ^ (if s q then count m q else 0)
            let mid = d.pow(q, sel_count);
            let step1 = bool_cases(
                d,
                &p,
                sq,
                &|d, x| {
                    let one_inner = d.num(1);
                    let pw = d.pow(q, cm);
                    let left = d.bool_select_nat(x, pw, one_inner);
                    let z = d.zero();
                    let sel_inner = d.bool_select_nat(x, cm, z);
                    let right = d.pow(q, sel_inner);
                    d.eq(left, right)
                },
                // s q = false: `1 = q ^ 0`.
                &|d| {
                    let pow_zero = d.lemma(p.pow_zero, &[q]);
                    let zero_inner = d.zero();
                    let q_pow_zero = d.pow(q, zero_inner);
                    let one_inner = d.num(1);
                    d.symm(q_pow_zero, one_inner, pow_zero)
                },
                // s q = true: both sides are `q ^ count m q`.
                &|d| {
                    let pw = d.pow(q, cm);
                    d.refl(pw)
                },
            );

            // q ^ (if s q then count m q else 0) = q ^ count (restrict m s) q
            let hcr = d.lemma(p.multiset_count_restrict, &[m, s, q]);
            let back = d.symm(sel_count, cr, hcr);
            let end = d.pow(q, cr);
            let step2 = d.congr(sel_count, cr, back, &|d, y| d.pow(q, y));

            let (_, body) = d.chain(start, &[(mid, step1), (end, step2)]);
            d.lam_fv(q_fv, nat, body)
        };
        let proof = d.lemma(p.prod_range_congr, &[f, g, b, pointwise]);
        declare_forall(
            d,
            p.multiset_prod_sel_eq_prod_restrict,
            &[(m_fv, ms), (s_fv, sty)],
            stmt,
            proof,
        )?;
    }

    // prodSel_all : ∀ m, Eq (prodSel m (fun _ => true)) (prod m) — refl.
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let all = {
            let q_fv = d.fresh_fvar();
            let t = d.bool_true();
            d.lam_fv(q_fv, nat, t)
        };
        let lhs = ms_prod_sel(d, &p, m, all);
        let rhs = ms_prod(d, &p, m);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        declare_forall(d, p.multiset_prod_sel_all, &[(m_fv, ms)], stmt, proof)?;
    }

    // prodSel_empty : ∀ m, Eq (prodSel m Subsets.empty) 1
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let empty = d.kernel().const_(p.subsets_empty, vec![]);
        let lhs = ms_prod_sel(d, &p, m, empty);
        let one = d.num(1);
        let stmt = d.eq(lhs, one);

        let f = select_factor(d, &p, m, empty);
        let g = {
            let q_fv = d.fresh_fvar();
            let one_inner = d.num(1);
            d.lam_fv(q_fv, nat, one_inner)
        };
        let b = ms_bound(d, &p, m);
        let pointwise = {
            let q_fv = d.fresh_fvar();
            let one_inner = d.num(1);
            let body = d.refl(one_inner);
            d.lam_fv(q_fv, nat, body)
        };
        let congr_step = d.lemma(p.prod_range_congr, &[f, g, b, pointwise]);
        let collapse = d.lemma(p.subsets_prod_range_one, &[b]);
        let mid = prod_range(d, &p, g, b);
        let proof = d.trans(lhs, mid, one, congr_step, collapse);
        declare_forall(d, p.multiset_prod_sel_empty, &[(m_fv, ms)], stmt, proof)?;
    }

    // prodSel_congr : ∀ m s t, (∀ q, Eq Bool (s q) (t q)) →
    //   Eq (prodSel m s) (prodSel m t)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);

        let hyp_ty = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let sq = d.apply(s, &[q]);
            let tq = d.apply(t, &[q]);
            let body = d.bool_eq(sq, tq);
            d.pi_fv(q_fv, nat, body)
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let lhs = ms_prod_sel(d, &p, m, s);
        let rhs = ms_prod_sel(d, &p, m, t);
        let stmt = d.eq(lhs, rhs);

        let f = select_factor(d, &p, m, s);
        let g = select_factor(d, &p, m, t);
        let b = ms_bound(d, &p, m);
        let pointwise = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let cm = ms_count(d, &p, m, q);
            let powered = d.pow(q, cm);
            let one = d.num(1);
            let sq = d.apply(s, &[q]);
            let tq = d.apply(t, &[q]);
            let hq = d.apply(h, &[q]);
            let start = d.bool_select_nat(sq, powered, one);
            let motive = d.bool_eq_motive(sq, &|d, x| {
                let pw = d.pow(q, cm);
                let one_inner = d.num(1);
                let right = d.bool_select_nat(x, pw, one_inner);
                d.eq(start, right)
            });
            let refl_case = d.refl(start);
            let body = d.bool_transport(sq, motive, refl_case, tq, hq);
            d.lam_fv(q_fv, nat, body)
        };
        let proof = d.lemma(p.prod_range_congr, &[f, g, b, pointwise]);
        declare_forall(
            d,
            p.multiset_prod_sel_congr,
            &[(m_fv, ms), (s_fv, sty), (t_fv, sty), (h_fv, hyp_ty)],
            stmt,
            proof,
        )?;
    }

    // prodSel_dvd_prod : ∀ m s, dvd (prodSel m s) (prod m)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);

        let lhs = ms_prod_sel(d, &p, m, s);
        let rhs = ms_prod(d, &p, m);
        let stmt = d.dvd(lhs, rhs);

        let f = select_factor(d, &p, m, s);
        let g = count_pow_factor(d, &p, m);
        let b = ms_bound(d, &p, m);
        let pointwise = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let cm = ms_count(d, &p, m, q);
            let sq = d.apply(s, &[q]);
            let body = bool_cases(
                d,
                &p,
                sq,
                &|d, x| {
                    let pw = d.pow(q, cm);
                    let one_inner = d.num(1);
                    let left = d.bool_select_nat(x, pw, one_inner);
                    let pw2 = d.pow(q, cm);
                    d.dvd(left, pw2)
                },
                // s q = false: `dvd 1 (q ^ count m q)`. `Nat.mul` recurses on
                // its RIGHT argument, so `mul 1 x` is STUCK for a symbolic `x`
                // and the witness equation needs `one_mul`, not reduction.
                &|d| {
                    let pw = d.pow(q, cm);
                    let one_mul = d.lemma(p.one_mul, &[pw]);
                    let one_again = d.num(1);
                    let product = d.mul(one_again, pw);
                    let eq_proof = d.symm(product, pw, one_mul);
                    let one_final = d.num(1);
                    dvd_intro(d, one_final, pw, pw, eq_proof)
                },
                // s q = true: `dvd x x`.
                &|d| {
                    let pw = d.pow(q, cm);
                    d.lemma(p.dvd_refl, &[pw])
                },
            );
            d.lam_fv(q_fv, nat, body)
        };
        let proof = d.lemma(p.prod_range_dvd_prod_range, &[f, g, b, pointwise]);
        declare_forall(
            d,
            p.multiset_prod_sel_dvd_prod,
            &[(m_fv, ms), (s_fv, sty)],
            stmt,
            proof,
        )?;
    }

    Ok(())
}

fn declare_injectivity(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let ms = multiset_ty(d, &p);
    let sty = set_ty(d);

    // prodSel_injective : ∀ m s t,
    //   (∀ q, Lt 0 (count m q) → prime_condition q) →
    //   Eq (prodSel m s) (prodSel m t) →
    //   ∀ q, Lt 0 (count m q) → Eq Bool (s q) (t q)
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let hp_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let c = ms_count(d, &p, m, x);
        let zero = d.zero();
        let pos = d.lt(zero, c);
        let concl = prime_condition(d, &p, x);
        let body = d.arrow(pos, concl);
        d.pi_fv(x_fv, nat, body)
    };
    let hp_fv = d.fresh_fvar();
    let hp = d.kernel().fvar(hp_fv);

    let ps = ms_prod_sel(d, &p, m, s);
    let pt = ms_prod_sel(d, &p, m, t);
    let heq_ty = d.eq(ps, pt);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let cm = ms_count(d, &p, m, q);
    let zero = d.zero();
    let hpos_ty = d.lt(zero, cm);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let sq = d.apply(s, &[q]);
    let tq = d.apply(t, &[q]);
    let goal = d.bool_eq(sq, tq);

    let rs = ms_restrict(d, &p, m, s);
    let rt = ms_restrict(d, &p, m, t);

    // The prime-support hypothesis transfers to each restriction.
    let restricted_prime = |d: &mut NatDev<'_>, sel: ExprId| -> ExprId {
        let r = ms_restrict(d, &p, m, sel);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let cr = ms_count(d, &p, r, x);
        let z = d.zero();
        let pos_ty = d.lt(z, cr);
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        let lifted = d.lemma(p.multiset_count_restrict_pos, &[m, sel, x, hx]);
        let applied = d.apply(hp, &[x, lifted]);
        let inner = d.lam_fv(hx_fv, pos_ty, applied);
        d.lam_fv(x_fv, nat, inner)
    };
    let hs_prime = restricted_prime(d, s);
    let ht_prime = restricted_prime(d, t);

    // prod (restrict m s) = prodSel m s = prodSel m t = prod (restrict m t)
    let prod_rs = ms_prod(d, &p, rs);
    let prod_rt = ms_prod(d, &p, rt);
    let hs_eq = d.lemma(p.multiset_prod_sel_eq_prod_restrict, &[m, s]);
    let ht_eq = d.lemma(p.multiset_prod_sel_eq_prod_restrict, &[m, t]);
    let back = d.symm(ps, prod_rs, hs_eq);
    let (_, prod_eq) = d.chain(prod_rs, &[(ps, back), (pt, heq), (prod_rt, ht_eq)]);

    // Uniqueness of prime factorization, at `q`.
    let counts_eq = d.lemma(
        p.multiset_count_eq_of_prod_eq,
        &[rs, rt, hs_prime, ht_prime, prod_eq, q],
    );

    // Rewrite both counts through `count_restrict` and read the `Bool` back.
    let hcs = d.lemma(p.multiset_count_restrict, &[m, s, q]);
    let hct = d.lemma(p.multiset_count_restrict, &[m, t, q]);
    let cs = ms_count(d, &p, rs, q);
    let ct = ms_count(d, &p, rt, q);
    let sel_s = {
        let z = d.zero();
        d.bool_select_nat(sq, cm, z)
    };
    let sel_t = {
        let z = d.zero();
        d.bool_select_nat(tq, cm, z)
    };
    let back_s = d.symm(cs, sel_s, hcs);
    let (_, sel_eq) = d.chain(sel_s, &[(cs, back_s), (ct, counts_eq), (sel_t, hct)]);
    let proof = d.lemma(p.bool_select_nat_inj_of_pos, &[cm, hpos, sq, tq, sel_eq]);

    declare_forall(
        d,
        p.multiset_prod_sel_injective,
        &[
            (m_fv, ms),
            (s_fv, sty),
            (t_fv, sty),
            (hp_fv, hp_ty),
            (heq_fv, heq_ty),
            (q_fv, nat),
            (hpos_fv, hpos_ty),
        ],
        goal,
        proof,
    )
}

/// Everything in this module, in dependency order. The driver names the step it
/// failed at rather than propagating an opaque `TypeMismatch` out of a
/// twelve-declaration build — one bad declaration poisons the whole shared
/// prelude, so the failure otherwise says nothing about WHICH declaration is
/// broken (`arith_functions_family.rs` records the same reasoning).
///
/// # Errors
///
/// Returns the trusted gate's rejection, after printing the failing step's
/// label and the rendered mismatch.
pub(super) fn declare_multiset_select_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    type Step = fn(&mut NatDev<'_>, &NatPrelude) -> Result<(), KernelError>;
    let steps: [(&str, Step); 5] = [
        ("dvd laws", declare_dvd_laws),
        ("definitions", declare_definitions),
        ("restrict laws", declare_restrict_laws),
        ("prodSel laws", declare_prod_sel_laws),
        ("injectivity", declare_injectivity),
    ];
    for (label, step) in steps {
        if let Err(e) = step(d, p) {
            let rendered = d.explain(&e);
            eprintln!("multiset_select: step `{label}` was rejected:\n  {rendered}");
            return Err(e);
        }
    }
    Ok(())
}
