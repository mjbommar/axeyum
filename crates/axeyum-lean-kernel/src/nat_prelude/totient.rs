//! `Nat.countRange` — the counting primitive nothing in this kernel had
//! before — and Euler's totient built on top of it.
//!
//! [`declare_count_range`] is `countRange p n := |{k < n : p k = true}|`, by
//! structural recursion on `n` (mirrors [`super::defs::declare_finite_ranges`]'s
//! `sumRange`, substituting the accumulated term for
//! [`NatOps::bool_select_nat`]'s `1`/`0` selection). [`declare_count_range_le`]
//! is the only non-defeq law this file needed for `countRange` itself:
//! `countRange p n ≤ n`, by induction, each step bounded by
//! `bool_select_nat _ 1 0 ≤ 1` (a direct `Bool.rec`, no fact about which
//! branch fires — the same shape as
//! [`super::transposition::bool_select_nat_lt`]).
//!
//! [`declare_totient`] is `totient n := countRange (fun k => beq (gcd k n) 1)
//! n` — counting residues in `[0,n)` coprime to `n`. This matches the
//! textbook `[1,n]` convention for every `n`: `k = 0` is only coprime to `n`
//! when `n = 1` (`gcd 0 n = n` via `gcd_zero_left`), and `n` itself is out of
//! range but was never coprime to itself for `n > 1` either. Hand-checked
//! values, verified by the kernel's own `def_eq` (see
//! `totient_computes_on_small_numerals` in `nat_prelude_tests.rs`):
//! `totient 1 = 1` (the range is `{0}`, `gcd 0 1 = 1`), `totient 6 = 2`
//! (`{1,5}` of `{0,..,5}` are coprime to 6), `totient 9 = 6` (`{1,2,4,5,7,8}`).
//!
//! [`declare_count_range_congr`] is `countRange_congr : (∀ i, f i = g i) →
//! countRange f n = countRange g n` — the unconditional pointwise congruence
//! `sumRange_congr` (`algebra.rs`) already has, ported to `countRange`'s
//! `Bool`-valued predicate via [`bool_congr_nat`] (below) at each induction
//! step's `bool_select_nat` term. Landed first, per the task's own
//! instruction to land `countRange` companions alone if nothing else does:
//! `countRange` was hours old and had almost no laws.
//!
//! [`declare_count_range_split`] is `countRange_split : countRange f (m+j) =
//! countRange f m + countRange (fun k => f (m+k)) j` — the `countRange`
//! analogue of `sumRange_split` (`rectangle.rs`), copied proof-shape and
//! all: induction on `j` alone, `f`/`m` held fixed, never touching
//! `Nat.sub`. This is the range-splitting building block a subset
//! enumeration would need to reason about `countRange` over a shifted
//! sub-range.
//!
//! [`declare_beq_eq_false_of_ne`] is the converse of the existing
//! `ne_of_beq_eq_false`: `Not (Eq a b) → beq a b = false`. It closes the
//! boolean/propositional bridge from the other side, by *deciding* `beq a b`
//! itself (a direct `Bool.rec` into `Or (_ = true) (_ = false)`, fully
//! constructive — `Bool` has exactly two constructors, this is case analysis,
//! not excluded middle) and refuting the `true` branch with
//! `eq_of_beq_eq_true`.
//!
//! [`declare_count_range_eq_pred_of_only_zero_false`] is the counting lemma
//! `totient_prime` rests on: if `f` is `false` at `0` and `true` everywhere
//! else in `[0, succ n)`, then `countRange f (succ n) = n` — one short of the
//! range's length, for exactly the one excluded point. Proved by induction on
//! `n`, restricting the bound hypothesis at each step
//! (`le_step`, the same restriction fermat.rs's `dvd_sum_range_of_forall_lt`
//! uses) and deciding the new top element via the hypothesis applied at
//! `k = succ n`.
//!
//! [`declare_totient_prime`] assembles these: `Prime p → totient p = p - 1`.
//! Built entirely in terms of `n := succ (pred p)` (via `pos_implies_succ_pred`,
//! copied locally exactly as `fermat.rs`'s own doc explains its convention),
//! so the counting lemma sees a literal successor, and transported back to
//! `p` only at the very end. The boundary at `k = 0` needs `p ≠ 1`, extracted
//! from primality's `2 ≤ p` conjunct via a direct defeq: `Le 2 1` unfolds to
//! `Lt 1 1` (`Lt a b := Le (succ a) b`), which `lt_irrefl` refutes with no
//! extra lemma.
//!
//! ## What does not land here
//!
//! Euler's theorem itself (`gcd a n = 1 → a^φ(n) ≡ 1 [n]`) needs a
//! permutation/pairing argument over the *subset* of residues coprime to
//! `n` — not a full contiguous range the way Fermat's and Wilson's proofs use
//! (`Int.prod_range_pairing_collapse`, `int_prelude/wilson.rs`). Building that
//! subset-permutation machinery is a separate, larger slice; nothing here
//! depends on it and nothing here builds it.

use super::NatPrelude;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ============================================================================
// Local copies of `fermat.rs`'s primality helpers (that module's own
// convention: local copies per file rather than a shared private module).
// ============================================================================

/// `False.rec (fun _ => target) false_proof : target`.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `2 ≤ x`, `∀ c, c ∣ x → c = 1 ∨ c = x`.
fn prime_parts(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);
    let two_le = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hyp = d.dvd(c, x);
    let is_one = d.eq(c, one);
    let is_x = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[is_one, is_x]);
    let inner = d.arrow(hyp, disjunction);
    let divisor_clause = d.pi_fv(c_fv, nat, inner);
    (two_le, divisor_clause)
}

/// `(2 ≤ x) ∧ (∀ c, c ∣ x → c = 1 ∨ c = x)`.
fn prime_ty(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let (two_le, divisor_clause) = prime_parts(d, p, x);
    d.const_app(p.logic.and, &[two_le, divisor_clause])
}

/// `prime x → Lt zero x`.
fn prime_pos(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, prime_proof: ExprId) -> ExprId {
    let (two_le_ty, divisor_clause_ty) = prime_parts(d, p, x);
    let two_le = and_left(d, two_le_ty, divisor_clause_ty, prime_proof);
    let one = d.num(1);
    let two = d.num(2);
    let one_le_two = d.lemma(p.le_succ, &[one]);
    d.lemma(p.le_trans, &[one, two, x, one_le_two, two_le])
}

/// `Lt zero n → Eq n (succ (pred n))`, by applying the declared
/// `Nat.succ_pred_of_pos` theorem (`finite.rs`).
fn pos_implies_succ_pred(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.lemma(p.succ_pred_of_pos, &[n])
}

// ============================================================================
// `Nat.countRange`.
// ============================================================================

/// `countRange(d, p, f, n)`, i.e. `d.const_app(p.count_range, &[f, n])`.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `Nat.countRange : (Nat → Bool) → Nat → Nat := fun p n =>
///   Nat.rec 0 (fun j ih => ih + bool_select_nat (p j) 1 0) n`.
///
/// Structural recursion on `n`, exactly [`super::defs::declare_finite_ranges`]'s
/// `sumRange` shape with the accumulated term replaced by the computational
/// `if p j then 1 else 0`.
pub(super) fn declare_count_range(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let base = d.zero();
    let step = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let one = d.num(1);
        let zero = d.zero();
        let increment = d.bool_select_nat(fj, one, zero);
        let body = d.add(ih, increment);
        let with_ih = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, with_ih)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let one_lvl = d.level_one();
    let rec = d.kernel().const_(p.rec, vec![one_lvl]);
    let body = d.apply(rec, &[motive, base, step, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, pred_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, nat);
        d.arrow(pred_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.count_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(12),
    })?;
    Ok(())
}

/// `countRange_zero`/`countRange_succ`: both hold by `Eq.refl`, mirroring
/// `sumRange_zero`/`sumRange_succ` in `defs.rs`.
pub(super) fn declare_count_range_defining_equations(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero = d.zero();
        let lhs = count_range(d, &p, f, zero);
        let stmt = d.eq(lhs, zero);
        let proof = d.refl(zero);
        let ty = d.pi_fv(f_fv, pred_ty, stmt);
        let value = d.lam_fv(f_fv, pred_ty, proof);
        d.declare_theorem(p.count_range_zero, ty, value)?;
    }
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = count_range(d, &p, f, sn);
        let prior = count_range(d, &p, f, n);
        let fn_at_n = d.apply(f, &[n]);
        let one = d.num(1);
        let zero = d.zero();
        let increment = d.bool_select_nat(fn_at_n, one, zero);
        let rhs = d.add(prior, increment);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, stmt);
            d.pi_fv(f_fv, pred_ty, with_n)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(f_fv, pred_ty, with_n)
        };
        d.declare_theorem(p.count_range_succ, ty, value)?;
    }
    Ok(())
}

/// `ha : Le zero one, hb : Le one one ⊢ Le (bool_select_nat cond 1 0) 1`, for
/// an arbitrary `cond : Bool` — direct `Bool.rec`, no fact about which branch
/// fires. Mirrors `transposition.rs`'s `bool_select_nat_lt`.
fn count_step_le_one(d: &mut NatDev<'_>, p: &NatPrelude, cond: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let one = d.num(1);
    let zero = d.zero();
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let one_inner = d.num(1);
        let zero_inner = d.zero();
        let sv = d.bool_select_nat(sel, one_inner, zero_inner);
        let one_bound = d.num(1);
        let body = d.le(sv, one_bound);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let false_case = d.lemma(p.zero_le, &[one]);
    let true_case = d.lemma(p.le_refl, &[one]);
    let _ = zero; // used only inside the motive closure above
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, false_case, true_case, cond])
}

/// `Nat.countRange_le : ∀ p n, Le (countRange p n) n`, by induction on `n`.
pub(super) fn declare_count_range_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let cr = count_range(d, &p, f, x);
        d.le(cr, x)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            d.lemma(p.le_refl, &[zero])
        },
        &|d, m, ih| {
            let cond = d.apply(f, &[m]);
            let bound = count_step_le_one(d, &p, cond);
            let cr_m = count_range(d, &p, f, m);
            let one = d.num(1);
            let zero = d.zero();
            let inc = d.bool_select_nat(cond, one, zero);
            let step1 = d.lemma(p.add_le_add_right, &[inc, cr_m, m, ih]);
            let one2 = d.num(1);
            let step2 = d.lemma(p.add_le_add_left, &[m, inc, one2, bound]);
            let cr_m_plus_inc = d.add(cr_m, inc);
            let m_plus_inc = d.add(m, inc);
            let one3 = d.num(1);
            let m_plus_one = d.add(m, one3);
            d.lemma(
                p.le_trans,
                &[cr_m_plus_inc, m_plus_inc, m_plus_one, step1, step2],
            )
        },
        n,
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, pred_ty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, pred_ty, with_n)
    };
    d.declare_theorem(p.count_range_le, ty, value)
}

/// `Nat.countRange_congr : ∀ f g n, (∀ i, Eq Bool (f i) (g i)) →
/// Eq Nat (countRange f n) (countRange g n)`.
///
/// By induction on `n`, exactly `sumRange_congr`'s shape (`algebra.rs`): base
/// case `Eq.refl zero`; step combines the IH (`countRange f j = countRange g
/// j`, congr'd through `add _ (bool_select_nat (f j) 1 0)`) with the
/// pointwise hypothesis at `j` pushed through `bool_select_nat` via
/// [`bool_congr_nat`] — the Bool-domain, Nat-codomain congruence this file
/// already built for `countRange_eq_pred_of_only_zero_false`. Unconditional
/// (needs `f i = g i` at every `i`, not just `i < n`): nothing downstream so
/// far needs the bounded form `sumRange` also carries
/// (`sumRange_congr_lt`) — add it if a future proof does.
pub(super) fn declare_count_range_congr(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

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
        let eq = d.bool_eq(fi, gi);
        d.pi_fv(i_fv, nat, eq)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| {
        let lhs = count_range(d, &p, f, x);
        let rhs = count_range(d, &p, g, x);
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
            let f_prior = count_range(d, &p, f, j);
            let g_prior = count_range(d, &p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let one = d.num(1);
            let zero = d.zero();
            let f_sel = d.bool_select_nat(fj, one, zero);

            let start = d.add(f_prior, f_sel);
            let mid = d.add(g_prior, f_sel);
            let h1 = d.congr(f_prior, g_prior, ih, &|d, t| d.add(t, f_sel));

            let one2 = d.num(1);
            let zero2 = d.zero();
            let g_sel = d.bool_select_nat(gj, one2, zero2);
            let end = d.add(g_prior, g_sel);
            let pointwise_j = d.apply(h, &[j]);
            let h2 = bool_congr_nat(d, fj, gj, pointwise_j, &|d, x| {
                let one_inner = d.num(1);
                let zero_inner = d.zero();
                let sv = d.bool_select_nat(x, one_inner, zero_inner);
                d.add(g_prior, sv)
            });

            let (_e, proof) = d.chain(start, &[(mid, h1), (end, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let with_h = d.pi_fv(h_fv, pointwise, stmt);
        let over_n = d.pi_fv(n_fv, nat, with_h);
        let over_g = d.pi_fv(g_fv, pred_ty, over_n);
        d.pi_fv(f_fv, pred_ty, over_g)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, pointwise, proof);
        let over_n = d.lam_fv(n_fv, nat, with_h);
        let over_g = d.lam_fv(g_fv, pred_ty, over_n);
        d.lam_fv(f_fv, pred_ty, over_g)
    };
    d.declare_theorem(p.count_range_congr, ty, value)
}

/// `fun k => f (add m k)` — `f` shifted so its own zero sits at `m`. Local
/// copy of `rectangle.rs`'s `shifted`, generic in codomain — that file's own
/// convention: private per-file copies rather than a shared module.
fn shifted_pred(d: &mut NatDev<'_>, f: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.add(m, k);
    let fmk = d.apply(f, &[mk]);
    d.lam_fv(k_fv, nat, fmk)
}

/// `Nat.countRange_split : ∀ f m j,
///   Eq Nat (countRange f (add m j)) (add (countRange f m) (countRange (fun k => f (add m k)) j))`.
///
/// By induction on `j`, `f` and `m` held fixed — exactly `sumRange_split`'s
/// shape (`rectangle.rs`), substituting each `sumRange` step for its
/// `countRange` counterpart (`add _ (bool_select_nat (f _) 1 0)` in place of
/// `add _ (f _)`). The step's two `bool_select_nat` conditions — `f (add m
/// k)` directly, and `(shifted f m) k` — are the SAME term up to defeq (pure
/// β-reduction of the shifted lambda), so unlike `countRange_congr` this
/// proof needs no `bool_congr_nat` bridge: both sides of the succ case's
/// defining equation unfold to the identical `bool_select_nat` application,
/// exactly as `sumRange_split`'s own proof never separately names the
/// shifted function's value.
pub(super) fn declare_count_range_split(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let g = shifted_pred(d, f, m);
    let count_f_m = count_range(d, &p, f, m);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let bound = d.add(m, x);
        let lhs = count_range(d, &p, f, bound);
        let tail = count_range(d, &p, g, x);
        let rhs = d.add(count_f_m, tail);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, j);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let rhs = d.add(count_f_m, zero);
            let h = d.lemma(p.add_zero, &[count_f_m]);
            d.symm(rhs, count_f_m, h)
        },
        &|d, k, ih| {
            let mk = d.add(m, k);
            let fmk = d.apply(f, &[mk]);
            let one = d.num(1);
            let zero = d.zero();
            let f_sel = d.bool_select_nat(fmk, one, zero);

            let count_f_mk = count_range(d, &p, f, mk);
            let count_g_k = count_range(d, &p, g, k);
            let count_f_m_g_k = d.add(count_f_m, count_g_k);

            let start = d.add(count_f_mk, f_sel);
            let mid = d.add(count_f_m_g_k, f_sel);
            let h1 = d.congr(count_f_mk, count_f_m_g_k, ih, &|d, t| d.add(t, f_sel));

            let inner = d.add(count_g_k, f_sel);
            let end = d.add(count_f_m, inner);
            let h2 = d.lemma(p.add_assoc, &[count_f_m, count_g_k, f_sel]);

            let (_e, chained) = d.chain(start, &[(mid, h1), (end, h2)]);
            chained
        },
        j,
    );

    let ty = {
        let over_j = d.pi_fv(j_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_j);
        d.pi_fv(f_fv, pred_ty, over_m)
    };
    let value = {
        let over_j = d.lam_fv(j_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_j);
        d.lam_fv(f_fv, pred_ty, over_m)
    };
    d.declare_theorem(p.count_range_split, ty, value)
}

// ============================================================================
// `Nat.totient`.
// ============================================================================

/// `fun k => beq (gcd k n) 1`.
fn totient_predicate(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let g = d.gcd(k, n);
    let one = d.num(1);
    let body = d.beq(g, one);
    d.lam_fv(k_fv, nat, body)
}

/// `Nat.totient n := countRange (fun k => beq (gcd k n) 1) n`.
pub(super) fn declare_totient(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let f = totient_predicate(d, n);
    let body = count_range(d, &p, f, n);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.totient,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(13),
    })?;
    Ok(())
}

// ============================================================================
// `Nat.beq_eq_false_of_ne` — the converse of `ne_of_beq_eq_false`.
// ============================================================================

/// `h : Eq Nat a b ⊢ Eq Bool (f a) (f b)`, for `f : Nat → Bool` — the
/// Bool-codomain analogue of [`NatOps::congr`] (which is hardcoded to a
/// `Nat`-codomain `f`).
fn nat_congr_bool(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.transport(a, motive, refl_case, b, h)
}

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)`, for `f : Bool → Nat` — the
/// Nat-codomain analogue of [`NatOps::bool_symm`]/`bool_trans` (which are
/// hardcoded to `Prop`-valued motives, but their own `bool_transport` is
/// general enough for this too since `Eq Nat _ _` is itself a `Prop`).
fn bool_congr_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId
where
{
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `Nat.beq_eq_false_of_ne : ∀ a b, Not (Eq a b) → Eq Bool (beq a b) false`.
///
/// Decides `beq a b` itself via [`bool_true_or_false`](super::ops::bool_true_or_false): the `true` branch is
/// refuted by `eq_of_beq_eq_true` against the hypothesis (`False.rec` into the
/// goal); the `false` branch is the goal directly.
pub(super) fn declare_beq_eq_false_of_ne(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.beq_eq_false_of_ne, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let eq_ab = d.eq(a, b);
        let not_fv = d.fresh_fvar();
        let not_hyp = d.kernel().fvar(not_fv);

        let beq_ab = d.beq(a, b);
        let false_ = d.bool_false();
        let true_ = d.bool_true();
        let target = d.bool_eq(beq_ab, false_);
        let true_ty = d.bool_eq(beq_ab, true_);
        let false_ty2 = d.bool_eq(beq_ab, false_);

        let cases = bool_true_or_false(d, &p, beq_ab);

        let true_branch = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let eq_derived = d.lemma(p.eq_of_beq_eq_true, &[a, b, h]);
            let absurd = d.apply(not_hyp, &[eq_derived]);
            let body = ex_falso(d, &p, target, absurd);
            d.lam_fv(h_fv, true_ty, body)
        };
        let false_branch = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, false_ty2, h)
        };

        let motive_or = {
            let or_ty = d.const_app(p.logic.or, &[true_ty, false_ty2]);
            let anon = d.anon_name();
            d.kernel().lam(anon, or_ty, target, BinderInfo::Default)
        };
        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let body = d.apply(
            or_rec,
            &[
                true_ty,
                false_ty2,
                motive_or,
                true_branch,
                false_branch,
                cases,
            ],
        );

        let not_ty = d.const_app(p.logic.not, &[eq_ab]);
        let stmt = d.arrow(not_ty, target);
        let proof = d.lam_fv(not_fv, not_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.countRange_eq_pred_of_only_zero_false`.
// ============================================================================

/// `∀ k, 0 < k → k < succ x → f k = true`.
fn hyp_at(d: &mut NatDev<'_>, f: ExprId, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let zero = d.zero();
    let pos_ty = d.lt(zero, k);
    let sx = d.succ(x);
    let bound_ty = d.lt(k, sx);
    let fk = d.apply(f, &[k]);
    let true_val = d.bool_true();
    let concl = d.bool_eq(fk, true_val);
    let inner = d.arrow(bound_ty, concl);
    let body = d.arrow(pos_ty, inner);
    d.pi_fv(k_fv, nat, body)
}

/// `Eq Bool (f 0) false`.
fn f0_false_ty(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let zero = d.zero();
    let f0 = d.apply(f, &[zero]);
    let false_val = d.bool_false();
    d.bool_eq(f0, false_val)
}

/// `Nat.countRange_eq_pred_of_only_zero_false : ∀ f n,
///   (∀ k, 0 < k → k < succ n → f k = true) → f 0 = false →
///   countRange f (succ n) = n`.
///
/// By induction on `n`. Base (`n = 0`): `countRange f 1` reduces to
/// `add zero (bool_select_nat (f 0) 1 0)`, and `zero_add` plus the hypothesis
/// `f 0 = false` (via [`bool_congr_nat`]) collapse it to `0`. Step: the
/// bound hypothesis restricts from `k < succ (succ m)` to `k < succ m` via
/// `le_step` (the same restriction `fermat.rs`'s `dvd_sum_range_of_forall_lt`
/// uses), so the IH applies; the new top element `f (succ m)` is decided
/// `true` by the hypothesis at `k = succ m` directly.
pub(super) fn declare_count_range_eq_pred_of_only_zero_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let hyp = hyp_at(d, f, x);
        let f0 = f0_false_ty(d, f);
        let sx = d.succ(x);
        let cr = count_range(d, &p, f, sx);
        let concl = d.eq(cr, x);
        let inner = d.arrow(f0, concl);
        d.arrow(hyp, inner)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero0 = d.zero();
            let hyp_ty0 = hyp_at(d, f, zero0);
            let hyp_fv = d.fresh_fvar();
            let _hyp = d.kernel().fvar(hyp_fv);
            let f0_ty = f0_false_ty(d, f);
            let f0_fv = d.fresh_fvar();
            let f0_hyp = d.kernel().fvar(f0_fv);

            let zero = d.zero();
            let fz = d.apply(f, &[zero]);
            let false_v = d.bool_false();
            let one_v = d.num(1);
            let zero_v = d.zero();
            let sel = d.bool_select_nat(fz, one_v, zero_v);
            let congr_sel = bool_congr_nat(d, fz, false_v, f0_hyp, &|d, x| {
                let one_inner = d.num(1);
                let zero_inner = d.zero();
                d.bool_select_nat(x, one_inner, zero_inner)
            });
            let add_zero_sel = d.add(zero, sel);
            let zero_add_sel = d.lemma(p.zero_add, &[sel]);
            let one_v2 = d.num(1);
            let zero_v2 = d.zero();
            let sel_false = d.bool_select_nat(false_v, one_v2, zero_v2);
            let (_e, eq_final) =
                d.chain(add_zero_sel, &[(sel, zero_add_sel), (sel_false, congr_sel)]);

            let with_f0 = d.lam_fv(f0_fv, f0_ty, eq_final);
            d.lam_fv(hyp_fv, hyp_ty0, with_f0)
        },
        &|d, m, ih| {
            let sm = d.succ(m);
            let hyp2_ty = hyp_at(d, f, sm);
            let hyp2_fv = d.fresh_fvar();
            let hyp2 = d.kernel().fvar(hyp2_fv);
            let f0_ty = f0_false_ty(d, f);
            let f0_fv = d.fresh_fvar();
            let f0_hyp = d.kernel().fvar(f0_fv);

            // Restrict `hyp2` (bound `succ (succ m)`) to `hyp_at(m)` (bound
            // `succ m`), for the IH.
            let restricted = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let zero = d.zero();
                let pos_ty = d.lt(zero, k);
                let bound_ty = d.lt(k, sm);
                let pos_fv = d.fresh_fvar();
                let pos_hyp = d.kernel().fvar(pos_fv);
                let bound_fv = d.fresh_fvar();
                let bound_hyp = d.kernel().fvar(bound_fv);
                let succ_k = d.succ(k);
                let lifted_bound = d.lemma(p.le_step, &[succ_k, sm, bound_hyp]);
                let applied = d.apply(hyp2, &[k, pos_hyp, lifted_bound]);
                let with_bound = d.lam_fv(bound_fv, bound_ty, applied);
                let with_pos = d.lam_fv(pos_fv, pos_ty, with_bound);
                d.lam_fv(k_fv, nat, with_pos)
            };
            let ih_applied = d.apply(ih, &[restricted, f0_hyp]);

            // `f (succ m) = true`, from `hyp2` at `k = succ m`.
            let ssm = d.succ(sm);
            let pos_sm = d.zero_lt_succ(m);
            let lt_sm_ssm = d.lemma(p.le_refl, &[ssm]);
            let f_sm_true = d.apply(hyp2, &[sm, pos_sm, lt_sm_ssm]);

            let count_range_f_sm = count_range(d, &p, f, sm);
            let fsm = d.apply(f, &[sm]);
            let one_v = d.num(1);
            let zero_v = d.zero();
            let sel2 = d.bool_select_nat(fsm, one_v, zero_v);
            let start = d.add(count_range_f_sm, sel2);

            let m_plus_sel2 = d.add(m, sel2);
            let step1 = d.congr(count_range_f_sm, m, ih_applied, &|d, x| {
                let sel2_inner = sel2;
                d.add(x, sel2_inner)
            });

            let true_v = d.bool_true();
            let one_v2 = d.num(1);
            let zero_v2 = d.zero();
            let sel2_true = d.bool_select_nat(true_v, one_v2, zero_v2);
            let m_plus_sel2_true = d.add(m, sel2_true);
            let step2 = bool_congr_nat(d, fsm, true_v, f_sm_true, &|d, x| {
                let one_inner = d.num(1);
                let zero_inner = d.zero();
                let sv = d.bool_select_nat(x, one_inner, zero_inner);
                d.add(m, sv)
            });

            let (_e, eq_final) = d.chain(start, &[(m_plus_sel2, step1), (m_plus_sel2_true, step2)]);

            let with_f0 = d.lam_fv(f0_fv, f0_ty, eq_final);
            d.lam_fv(hyp2_fv, hyp2_ty, with_f0)
        },
        n,
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, pred_ty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, pred_ty, with_n)
    };
    d.declare_theorem(p.count_range_eq_pred_of_only_zero_false, ty, value)
}

// ============================================================================
// `Nat.totient_prime`.
// ============================================================================

/// `Nat.totient_prime : Prime p → totient p = sub p 1`.
///
/// Built in terms of `n := succ (pred p)` (from positivity, exactly
/// `fermat.rs`'s technique) so `countRange_eq_pred_of_only_zero_false` sees a
/// literal successor; transported back to `p` only at the end.
pub(super) fn declare_totient_prime(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.totient_prime, 1, &|d, v| {
        let pp = v[0];
        let prime_ty_pp = prime_ty(d, &p, pp);
        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        // n := succ (pred pp), eq_n_pp : Eq n pp.
        let zero_lt_pp = prime_pos(d, &p, pp, prime_proof);
        let eq_pp_n_fn = pos_implies_succ_pred(d, &p, pp);
        let eq_pp_n = d.apply(eq_pp_n_fn, &[zero_lt_pp]);
        let m = d.pred(pp);
        let n = d.succ(m);
        let eq_n_pp = d.symm(pp, n, eq_pp_n);

        let transport_motive = d.eq_motive(pp, &|d, x| prime_ty(d, &p, x));
        let prime_proof_n = d.transport(pp, transport_motive, prime_proof, n, eq_pp_n);

        let f = totient_predicate(d, n);

        // `∀ k, 0 < k → k < n → f k = true`, from `coprime_of_lt_prime`.
        let hyp = {
            let nat = d.nat_ty();
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let zero = d.zero();
            let pos_ty = d.lt(zero, k);
            let bound_ty = d.lt(k, n);
            let pos_fv = d.fresh_fvar();
            let pos_hyp = d.kernel().fvar(pos_fv);
            let bound_fv = d.fresh_fvar();
            let bound_hyp = d.kernel().fvar(bound_fv);
            let gcd_eq_one = d.lemma(
                p.coprime_of_lt_prime,
                &[n, k, prime_proof_n, pos_hyp, bound_hyp],
            );
            let g = d.gcd(k, n);
            let one = d.num(1);
            let fk_true = d.lemma(p.beq_eq_true_of_eq, &[g, one, gcd_eq_one]);
            let with_bound = d.lam_fv(bound_fv, bound_ty, fk_true);
            let with_pos = d.lam_fv(pos_fv, pos_ty, with_bound);
            d.lam_fv(k_fv, nat, with_pos)
        };

        // `f 0 = false`, from `2 ≤ n` (hence `n ≠ 1`) and `gcd 0 n = n`.
        let f0_false = {
            let two_le_n = {
                let (two_le_ty, divisor_clause_ty) = prime_parts(d, &p, n);
                and_left(d, two_le_ty, divisor_clause_ty, prime_proof_n)
            };
            let not_eq_n_1 = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let one = d.num(1);
                let motive = d.eq_motive(n, &|d, x| {
                    let two = d.num(2);
                    d.le(two, x)
                });
                let transported = d.transport(n, motive, two_le_n, one, h);
                let one2 = d.num(1);
                let lt_irrefl_1 = d.lemma(p.lt_irrefl, &[one2]);
                let absurd = d.apply(lt_irrefl_1, &[transported]);
                let one3 = d.num(1);
                let eq_ty = d.eq(n, one3);
                d.lam_fv(h_fv, eq_ty, absurd)
            };
            let one = d.num(1);
            let beq_n_1_false = d.lemma(p.beq_eq_false_of_ne, &[n, one, not_eq_n_1]);

            let zero = d.zero();
            let one2 = d.num(1);
            let g0 = d.gcd(zero, n);
            let gcd_zero_n = d.lemma(p.gcd_zero_left, &[n]);
            let beq_g0_1 = d.beq(g0, one2);
            let one3 = d.num(1);
            let beq_n_1 = d.beq(n, one3);
            let congr_g0 = nat_congr_bool(d, g0, n, gcd_zero_n, &|d, x| {
                let one_inner = d.num(1);
                d.beq(x, one_inner)
            });
            let false_ = d.bool_false();
            d.bool_trans(beq_g0_1, beq_n_1, false_, congr_g0, beq_n_1_false)
        };

        let counting = d.lemma(
            p.count_range_eq_pred_of_only_zero_false,
            &[f, m, hyp, f0_false],
        );

        let final_motive = d.eq_motive(n, &|d, x| {
            let fx = totient_predicate(d, x);
            let cr = count_range(d, &p, fx, x);
            d.eq(cr, m)
        });
        let final_proof = d.transport(n, final_motive, counting, pp, eq_n_pp);

        let totient_pp = d.const_app(p.totient, &[pp]);
        let one = d.num(1);
        let sub_one = d.sub(pp, one);
        let target = d.eq(totient_pp, sub_one);
        let stmt = d.arrow(prime_ty_pp, target);
        let proof = d.lam_fv(prime_fv, prime_ty_pp, final_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `Nat.countRange` and its laws, `Nat.totient`,
/// `Nat.beq_eq_false_of_ne`, and `Nat.totient_prime`, in dependency order.
pub(super) fn declare_totient_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_count_range(d, p)?;
    declare_count_range_defining_equations(d, p)?;
    declare_count_range_le(d, p)?;
    declare_count_range_congr(d, p)?;
    declare_count_range_split(d, p)?;
    declare_totient(d, p)?;
    declare_beq_eq_false_of_ne(d, p)?;
    declare_count_range_eq_pred_of_only_zero_false(d, p)?;
    declare_totient_prime(d, p)?;
    Ok(())
}
