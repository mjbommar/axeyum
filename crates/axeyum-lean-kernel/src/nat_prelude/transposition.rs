//! `Nat.transposition i j k` — the swap map that exchanges `i` and `j` and
//! fixes everything else — plus the reusable object `wilson.rs`'s interior
//! collapse needs: its involution law, the injectivity/self-map laws that
//! follow from it, and the generic conjugation lemmas
//! (`Nat.conjugate_injective` / `Nat.conjugate_maps_into`) that transport
//! `InjectiveOn`/`MapsInto` across conjugation by *any* involutive self-map,
//! not just this concrete one.
//!
//! ## `Nat.transposition`
//!
//! Built the same way `int_prelude/prod.rs`'s `point_swap` and this module's
//! own `point_override` are: four nested `Nat.ble` cuts, never `Nat.beq`.
//! `point_swap` swaps the *values* of a supplied `f` at two positions;
//! `transposition` is the same case tree specialized to the identity
//! function, returning `j` at `i`, `i` at `j`, and `k` everywhere else, as a
//! **named** `Nat → Nat → Nat → Nat` definition — the piece `prodRange_swap`
//! does not give, since it takes its swapped function by *hypothesis* rather
//! than constructing one (`wilson.rs`'s module doc).
//!
//! `i < j` is required by [`declare_transposition_involutive`]'s statement
//! and the `_at_i`/`_at_j`/`_gt_j` correctness facts it is built from, the
//! same way `point_swap`'s own five correctness facts need `p < q` at the
//! boundary cases — the construction itself is silent about order, only the
//! *meaning* ("transposition of `i` and `j`") breaks without it.
//!
//! ## The involution, and injectivity for free
//!
//! `transposition_involutive` is proved by a full five-region case split on
//! `k` (`k < i`, `k = i`, `i < k < j`, `k = j`, `k > j`), reusing the same
//! `trichotomy`/`select_nat_true`/`select_nat_false` machinery `finite.rs`
//! already built for `compact`/`point_override`. Injectivity is **not** a
//! second case split: any involution is injective (`x = t(t(x))`, congruence
//! under `h : t(x) = t(y)` gives `t(t(x)) = t(t(y))`, cancel via the
//! involution law at `x` and at `y`), and [`injective_of_involutive`] is that
//! generic three-line argument, applied once for `Nat.transposition_injective`
//! (with `t := Nat.transposition i j`) and again inside
//! [`declare_conjugate_injective`] (with `t` an arbitrary parameter).
//! `Nat.transposition_maps_into` does not need the case split either — a
//! *bound* that holds for both branches of a `bool_select_nat` holds for the
//! selector regardless of which way it goes, so it is proved by `Bool.rec`
//! directly on each level's own condition, never by pinning the condition to
//! a literal (`bool_select_nat_lt`, below).
//!
//! ## `Nat.conjugate_injective` / `Nat.conjugate_maps_into`
//!
//! Stated over an arbitrary `t : Nat → Nat` satisfying `∀ x, t (t x) = x`
//! (never specialized to `Nat.transposition`), because the proof only ever
//! uses that law and `MapsInto t n` — never `transposition`'s own
//! construction. `conjugate_injective`'s route:
//! `t (σ (t a)) = t (σ (t b))` cancels the outer `t` via
//! [`injective_of_involutive`], giving `σ (t a) = σ (t b)`; `MapsInto t n`
//! places `t a`/`t b` inside `σ`'s injective domain, so `σ`'s own
//! `InjectiveOn` gives `t a = t b`; [`injective_of_involutive`] cancels once
//! more to reach `a = b`. `conjugate_maps_into` needs no involution at all —
//! three compositions of `MapsInto` hypotheses.

use super::NatPrelude;
use super::finite::{
    le_of_lt, restrict_ble_eq_false_of_lt, select_nat_false, select_nat_true, trichotomy,
};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Delta height for `Nat.transposition`: it calls only `Nat.ble` (height 1),
/// so any height strictly above that is sound; `2` keeps it adjacent.
const TRANSPOSITION_HEIGHT: u16 = 2;

// ---------------------------------------------------------------------------
// The raw case tree (mirrors `int_prelude/prod.rs`'s `ps_level4`/`ps_level3`/
// `ps_level2`/`point_swap`, specialized to the identity function: no `f` to
// apply, the literal `i`/`j`/`k` stand in for `f p`/`f q`/`f k`).
// ---------------------------------------------------------------------------

/// `transposition i j k`'s outermost (4th) layer: for `k > j`, `k`; for
/// `k = j`, `i`.
fn t_level4(d: &mut NatDev<'_>, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let le_k_j = d.ble(k, j);
    d.bool_select_nat(le_k_j, i, k)
}

/// `transposition i j k`'s 3rd layer: for `i < k < j`, `k`; else
/// [`t_level4`].
fn t_level3(d: &mut NatDev<'_>, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let level4 = t_level4(d, i, j, k);
    let sk = d.succ(k);
    let lt_k_j = d.ble(sk, j);
    d.bool_select_nat(lt_k_j, k, level4)
}

/// `transposition i j k`'s 2nd layer: for `k = i`, `j`; else [`t_level3`].
fn t_level2(d: &mut NatDev<'_>, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let level3 = t_level3(d, i, j, k);
    let le_k_i = d.ble(k, i);
    d.bool_select_nat(le_k_i, j, level3)
}

/// `transposition i j k` — `j` at `i`, `i` at `j`, `k` everywhere else (for
/// `i < j`, supplied by the caller). Four nested `Nat.ble` case-splits.
fn transposition(d: &mut NatDev<'_>, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let level2 = t_level2(d, i, j, k);
    let sk = d.succ(k);
    let lt_k_i = d.ble(sk, i);
    d.bool_select_nat(lt_k_i, k, level2)
}

/// Admit `Nat.transposition : Nat → Nat → Nat → Nat := fun i j k => <case tree>`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_transposition(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let body = transposition(d, i, j, k);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_j = d.lam_fv(j_fv, nat, with_k);
        d.lam_fv(i_fv, nat, with_j)
    };
    let ty = {
        let inner = d.arrow(nat, nat);
        let with_j = d.arrow(nat, inner);
        d.arrow(nat, with_j)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.transposition,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(TRANSPOSITION_HEIGHT),
    })
}

// ---------------------------------------------------------------------------
// The five correctness facts, mirroring `point_swap_eq_lt_p` / `_at_p` /
// `_between` / `_at_q` / `_gt_q` exactly (`f` erased: `f p`/`f q`/`f k`
// become the literals `i`/`j`/`k`).
// ---------------------------------------------------------------------------

/// `h : Lt k i ⊢ Eq Nat (transposition i j k) k`.
pub(crate) fn transposition_eq_lt_i(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let level2 = t_level2(d, i, j, k);
    let sk = d.succ(k);
    let lt_k_i = d.ble(sk, i);
    let lt_true = d.lemma(p.ble_eq_true_of_le, &[sk, i, h]);
    select_nat_true(d, lt_k_i, k, level2, lt_true)
}

/// `Eq Nat (transposition i j i) j` — unconditional.
pub(crate) fn transposition_eq_at_i(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    let level2 = t_level2(d, i, j, i);
    let level3 = t_level3(d, i, j, i);
    let si = d.succ(i);
    let lt_i_i = d.ble(si, i);
    let lt_succ_self_i = d.lemma(p.lt_succ_self, &[i]);
    let lt_false = restrict_ble_eq_false_of_lt(d, p, si, i, lt_succ_self_i);
    let step1 = select_nat_false(d, lt_i_i, i, level2, lt_false);
    let le_i_i = d.ble(i, i);
    let le_refl_i = d.lemma(p.le_refl, &[i]);
    let le_true = d.lemma(p.ble_eq_true_of_le, &[i, i, le_refl_i]);
    let step2 = select_nat_true(d, le_i_i, j, level3, le_true);
    let start = transposition(d, i, j, i);
    let (_, proof) = d.chain(start, &[(level2, step1), (j, step2)]);
    proof
}

/// `h1 : Lt i k, h2 : Lt k j ⊢ Eq Nat (transposition i j k) k`.
pub(crate) fn transposition_eq_between(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let level2 = t_level2(d, i, j, k);
    let level3 = t_level3(d, i, j, k);
    let level4 = t_level4(d, i, j, k);
    let sk = d.succ(k);

    let le_succ_k = d.lemma(p.le_succ, &[k]);
    let lt_i_sk = d.lemma(p.lt_of_lt_of_le, &[i, k, sk, h1, le_succ_k]);
    let lt_k_i = d.ble(sk, i);
    let lt_k_i_false = restrict_ble_eq_false_of_lt(d, p, sk, i, lt_i_sk);
    let step1 = select_nat_false(d, lt_k_i, k, level2, lt_k_i_false);

    let le_k_i = d.ble(k, i);
    let le_k_i_false = restrict_ble_eq_false_of_lt(d, p, k, i, h1);
    let step2 = select_nat_false(d, le_k_i, j, level3, le_k_i_false);

    let lt_k_j = d.ble(sk, j);
    let lt_k_j_true = d.lemma(p.ble_eq_true_of_le, &[sk, j, h2]);
    let step3 = select_nat_true(d, lt_k_j, k, level4, lt_k_j_true);

    let start = transposition(d, i, j, k);
    let (_, proof) = d.chain(start, &[(level2, step1), (level3, step2), (k, step3)]);
    proof
}

/// `h_ij : Lt i j ⊢ Eq Nat (transposition i j j) i`.
pub(crate) fn transposition_eq_at_j(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    h_ij: ExprId,
) -> ExprId {
    let level2 = t_level2(d, i, j, j);
    let level3 = t_level3(d, i, j, j);
    let level4 = t_level4(d, i, j, j);
    let sj = d.succ(j);

    let le_succ_j = d.lemma(p.le_succ, &[j]);
    let lt_i_sj = d.lemma(p.lt_of_lt_of_le, &[i, j, sj, h_ij, le_succ_j]);
    let lt_j_i = d.ble(sj, i);
    let lt_j_i_false = restrict_ble_eq_false_of_lt(d, p, sj, i, lt_i_sj);
    let step1 = select_nat_false(d, lt_j_i, j, level2, lt_j_i_false);

    let le_j_i = d.ble(j, i);
    let le_j_i_false = restrict_ble_eq_false_of_lt(d, p, j, i, h_ij);
    let step2 = select_nat_false(d, le_j_i, j, level3, le_j_i_false);

    let lt_succ_self_j = d.lemma(p.lt_succ_self, &[j]);
    let lt_j_j = d.ble(sj, j);
    let lt_j_j_false = restrict_ble_eq_false_of_lt(d, p, sj, j, lt_succ_self_j);
    let step3 = select_nat_false(d, lt_j_j, j, level4, lt_j_j_false);

    let le_refl_j = d.lemma(p.le_refl, &[j]);
    let le_j_j = d.ble(j, j);
    let le_j_j_true = d.lemma(p.ble_eq_true_of_le, &[j, j, le_refl_j]);
    let step4 = select_nat_true(d, le_j_j, i, j, le_j_j_true);

    let start = transposition(d, i, j, j);
    let (_, proof) = d.chain(
        start,
        &[
            (level2, step1),
            (level3, step2),
            (level4, step3),
            (i, step4),
        ],
    );
    proof
}

/// `h_ij : Lt i j, h : Lt j k ⊢ Eq Nat (transposition i j k) k`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn transposition_eq_gt_j(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    h_ij: ExprId,
    h: ExprId,
) -> ExprId {
    let level2 = t_level2(d, i, j, k);
    let level3 = t_level3(d, i, j, k);
    let level4 = t_level4(d, i, j, k);
    let sk = d.succ(k);

    let le_i_j = le_of_lt(d, p, i, j, h_ij);
    let lt_i_k = d.lemma(p.lt_of_le_of_lt, &[i, j, k, le_i_j, h]);

    let le_succ_k = d.lemma(p.le_succ, &[k]);
    let lt_i_sk = d.lemma(p.lt_of_lt_of_le, &[i, k, sk, lt_i_k, le_succ_k]);
    let lt_k_i = d.ble(sk, i);
    let lt_k_i_false = restrict_ble_eq_false_of_lt(d, p, sk, i, lt_i_sk);
    let step1 = select_nat_false(d, lt_k_i, k, level2, lt_k_i_false);

    let le_k_i = d.ble(k, i);
    let le_k_i_false = restrict_ble_eq_false_of_lt(d, p, k, i, lt_i_k);
    let step2 = select_nat_false(d, le_k_i, j, level3, le_k_i_false);

    let lt_j_sk = d.lemma(p.lt_of_lt_of_le, &[j, k, sk, h, le_succ_k]);
    let lt_k_j = d.ble(sk, j);
    let lt_k_j_false = restrict_ble_eq_false_of_lt(d, p, sk, j, lt_j_sk);
    let step3 = select_nat_false(d, lt_k_j, k, level4, lt_k_j_false);

    let le_k_j = d.ble(k, j);
    let le_k_j_false = restrict_ble_eq_false_of_lt(d, p, k, j, h);
    let step4 = select_nat_false(d, le_k_j, i, k, le_k_j_false);

    let start = transposition(d, i, j, k);
    let (_, proof) = d.chain(
        start,
        &[
            (level2, step1),
            (level3, step2),
            (level4, step3),
            (k, step4),
        ],
    );
    proof
}

// ---------------------------------------------------------------------------
// `Nat.transposition_involutive`
// ---------------------------------------------------------------------------

/// From `h1 : Eq Nat (transposition i j x) y` and
/// `h2 : Eq Nat (transposition i j y) z`, derive
/// `Eq Nat (transposition i j (transposition i j x)) z` — congruence under
/// `h1` gives `t(t x) = t y`, then `trans` with `h2`.
#[allow(clippy::too_many_arguments)]
fn close_involutive(
    d: &mut NatDev<'_>,
    i: ExprId,
    j: ExprId,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let tx = transposition(d, i, j, x);
    let ty = transposition(d, i, j, y);
    let ttx = transposition(d, i, j, tx);
    let congr_step = d.congr(tx, y, h1, &|d, w| transposition(d, i, j, w));
    d.trans(ttx, ty, z, congr_step, h2)
}

/// From `h : Eq Nat k c` and `at_c : Eq Nat (transposition i j (transposition
/// i j c)) c`, derive `Eq Nat (transposition i j (transposition i j k)) k` —
/// transport `at_c` backwards along `h`.
fn transport_involutive(
    d: &mut NatDev<'_>,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    c: ExprId,
    h: ExprId,
    at_c: ExprId,
) -> ExprId {
    let h_rev = d.symm(k, c, h);
    let motive = d.eq_motive(c, &|d, x| {
        let tx = transposition(d, i, j, x);
        let ttx = transposition(d, i, j, tx);
        d.eq(ttx, x)
    });
    d.transport(c, motive, at_c, k, h_rev)
}

/// `Nat.transposition_involutive : ∀ i j, Lt i j → ∀ k,
///   Eq Nat (transposition i j (transposition i j k)) k`.
///
/// A five-region case split on `k` (`Lt k i`, `Eq k i`, `Lt i k ∧ Lt k j`,
/// `Eq k j`, `Lt j k`), via nested `trichotomy`. The two equality leaves
/// transport [`transposition_eq_at_i`]/[`transposition_eq_at_j`] (stated at
/// the literal points `i`/`j`) out to the generic `k`; the other three reuse
/// [`transposition_eq_lt_i`]/`_between`/`_gt_j` directly, each closed by
/// [`close_involutive`] against itself (the identity holds at that point, so
/// the same fact serves as both halves of the two-step chain).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_transposition_involutive(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let h_ij_ty = d.lt(i, j);
    let hij_fv = d.fresh_fvar();
    let h_ij = d.kernel().fvar(hij_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let tk = transposition(d, i, j, k);
    let ttk = transposition(d, i, j, tk);
    let goal = d.eq(ttk, k);

    let lt_k_i = d.lt(k, i);
    let eq_k_i = d.eq(k, i);
    let lt_i_k = d.lt(i, k);
    let lt_k_j = d.lt(k, j);
    let eq_k_j = d.eq(k, j);
    let lt_j_k = d.lt(j, k);

    // --- region: k < i ---
    let branch_lt_i = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let fact = transposition_eq_lt_i(d, &p, i, j, k, h);
        let result = close_involutive(d, i, j, k, k, k, fact, fact);
        d.lam_fv(h_fv, lt_k_i, result)
    };

    // --- region: k = i ---
    let branch_eq_i = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let fact_at_i = transposition_eq_at_i(d, &p, i, j);
        let fact_at_j = transposition_eq_at_j(d, &p, i, j, h_ij);
        let at_i = close_involutive(d, i, j, i, j, i, fact_at_i, fact_at_j);
        let result = transport_involutive(d, i, j, k, i, h, at_i);
        d.lam_fv(h_fv, eq_k_i, result)
    };

    // --- region: i < k, split against j ---
    let branch_gt_i = {
        let hg_fv = d.fresh_fvar();
        let hg = d.kernel().fvar(hg_fv);

        let tri_inner = trichotomy(d, &p, j, k);

        let inner_lt_j = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let fact = transposition_eq_between(d, &p, i, j, k, hg, h2);
            let result = close_involutive(d, i, j, k, k, k, fact, fact);
            d.lam_fv(h2_fv, lt_k_j, result)
        };

        let inner_rest = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let inner_eq_j = {
                let h3_fv = d.fresh_fvar();
                let h3 = d.kernel().fvar(h3_fv);
                let fact_at_j = transposition_eq_at_j(d, &p, i, j, h_ij);
                let fact_at_i = transposition_eq_at_i(d, &p, i, j);
                let at_j = close_involutive(d, i, j, j, i, j, fact_at_j, fact_at_i);
                let result = transport_involutive(d, i, j, k, j, h3, at_j);
                d.lam_fv(h3_fv, eq_k_j, result)
            };
            let inner_gt_j = {
                let h3_fv = d.fresh_fvar();
                let h3 = d.kernel().fvar(h3_fv);
                let fact = transposition_eq_gt_j(d, &p, i, j, k, h_ij, h3);
                let result = close_involutive(d, i, j, k, k, k, fact, fact);
                d.lam_fv(h3_fv, lt_j_k, result)
            };

            let body = d.const_app(
                p.logic.or_elim,
                &[eq_k_j, lt_j_k, goal, h2, inner_eq_j, inner_gt_j],
            );
            let or_rest2_ty = d.const_app(p.logic.or, &[eq_k_j, lt_j_k]);
            d.lam_fv(h2_fv, or_rest2_ty, body)
        };

        let or_rest2_ty = d.const_app(p.logic.or, &[eq_k_j, lt_j_k]);
        let body = d.const_app(
            p.logic.or_elim,
            &[lt_k_j, or_rest2_ty, goal, tri_inner, inner_lt_j, inner_rest],
        );
        d.lam_fv(hg_fv, lt_i_k, body)
    };

    let branch_rest = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.const_app(
            p.logic.or_elim,
            &[eq_k_i, lt_i_k, goal, h, branch_eq_i, branch_gt_i],
        );
        let or_rest_ty = d.const_app(p.logic.or, &[eq_k_i, lt_i_k]);
        d.lam_fv(h_fv, or_rest_ty, body)
    };

    let tri_outer = trichotomy(d, &p, i, k);
    let or_rest_ty = d.const_app(p.logic.or, &[eq_k_i, lt_i_k]);
    let proof_body = d.const_app(
        p.logic.or_elim,
        &[
            lt_k_i,
            or_rest_ty,
            goal,
            tri_outer,
            branch_lt_i,
            branch_rest,
        ],
    );

    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof_body);
        let with_hij = d.lam_fv(hij_fv, h_ij_ty, with_k);
        let with_j = d.lam_fv(j_fv, nat, with_hij);
        d.lam_fv(i_fv, nat, with_j)
    };
    let ty = {
        let with_k = d.pi_fv(k_fv, nat, goal);
        let with_hij = d.arrow(h_ij_ty, with_k);
        let with_j = d.pi_fv(j_fv, nat, with_hij);
        d.pi_fv(i_fv, nat, with_j)
    };

    d.declare_theorem(p.transposition_involutive, ty, value)
}

// ---------------------------------------------------------------------------
// Injectivity of any involution — the generic argument, reused for
// `Nat.transposition_injective` and inside `Nat.conjugate_injective`.
// ---------------------------------------------------------------------------

/// From `t_inv : ∀ x, Eq Nat (t (t x)) x` and `h : Eq Nat (t x) (t y)`,
/// derive `Eq Nat x y` — any involution is injective:
/// `x = t(t x) = t(t y) = y`, the middle step by congruence under `h`.
fn injective_of_involutive(
    d: &mut NatDev<'_>,
    t: ExprId,
    t_inv: ExprId,
    x: ExprId,
    y: ExprId,
    h: ExprId,
) -> ExprId {
    let tx = d.apply(t, &[x]);
    let ty = d.apply(t, &[y]);
    let inv_x = d.apply(t_inv, &[x]);
    let inv_y = d.apply(t_inv, &[y]);
    let congr_step = d.congr(tx, ty, h, &|d, z| d.apply(t, &[z]));
    let ttx = d.apply(t, &[tx]);
    let tty = d.apply(t, &[ty]);
    let symm_inv_x = d.symm(ttx, x, inv_x);
    let step1 = d.trans(x, ttx, tty, symm_inv_x, congr_step);
    d.trans(x, tty, y, step1, inv_y)
}

/// `Nat.transposition_injective : ∀ i j n, Lt i j →
///   InjectiveOn (fun k => transposition i j k) n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_transposition_injective(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let h_ij_ty = d.lt(i, j);
    let hij_fv = d.fresh_fvar();
    let h_ij = d.kernel().fvar(hij_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sigma = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.transposition, &[i, j, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let concl = d.const_app(p.injective_on, &[sigma, n]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let han_ty = d.lt(a, n);
    let han_fv = d.fresh_fvar();
    let _han = d.kernel().fvar(han_fv);
    let hbn_ty = d.lt(b, n);
    let hbn_fv = d.fresh_fvar();
    let _hbn = d.kernel().fvar(hbn_fv);

    let sigma_a = d.const_app(p.transposition, &[i, j, a]);
    let sigma_b = d.const_app(p.transposition, &[i, j, b]);
    let heq_ty = d.eq(sigma_a, sigma_b);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let t = d.const_app(p.transposition, &[i, j]);
    let t_inv = d.const_app(p.transposition_involutive, &[i, j, h_ij]);
    let result = injective_of_involutive(d, t, t_inv, a, b, heq);

    let inner = d.lam_fv(heq_fv, heq_ty, result);
    let with_hbn = d.lam_fv(hbn_fv, hbn_ty, inner);
    let with_han = d.lam_fv(han_fv, han_ty, with_hbn);
    let with_b = d.lam_fv(b_fv, nat, with_han);
    let with_a = d.lam_fv(a_fv, nat, with_b);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, with_a);
        let with_hij = d.lam_fv(hij_fv, h_ij_ty, with_n);
        let with_j = d.lam_fv(j_fv, nat, with_hij);
        d.lam_fv(i_fv, nat, with_j)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, concl);
        let with_hij = d.arrow(h_ij_ty, with_n);
        let with_j = d.pi_fv(j_fv, nat, with_hij);
        d.pi_fv(i_fv, nat, with_j)
    };

    d.declare_theorem(p.transposition_injective, ty, value)
}

// ---------------------------------------------------------------------------
// `Nat.transposition_maps_into` — a bound, not a value, so `Bool.rec`
// directly on each level's own condition suffices; no case split on which
// branch fires.
// ---------------------------------------------------------------------------

/// `ha : Lt a n, hb : Lt b n ⊢ Lt (bool_select_nat cond a b) n`, for an
/// arbitrary `cond : Bool` — `Bool.rec` directly on `cond`, needing no fact
/// about which branch it actually selects.
#[allow(clippy::too_many_arguments)]
fn bool_select_nat_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let sv = d.bool_select_nat(sel, a, b);
        let body = d.lt(sv, n);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, hb, ha, cond])
}

#[allow(clippy::too_many_arguments)]
fn t_level4_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    n: ExprId,
    hi: ExprId,
    hk: ExprId,
) -> ExprId {
    let cond = d.ble(k, j);
    bool_select_nat_lt(d, p, cond, i, k, n, hi, hk)
}

#[allow(clippy::too_many_arguments)]
fn t_level3_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    n: ExprId,
    hi: ExprId,
    hk: ExprId,
) -> ExprId {
    let level4 = t_level4(d, i, j, k);
    let level4_lt = t_level4_lt(d, p, i, j, k, n, hi, hk);
    let sk = d.succ(k);
    let cond = d.ble(sk, j);
    bool_select_nat_lt(d, p, cond, k, level4, n, hk, level4_lt)
}

#[allow(clippy::too_many_arguments)]
fn t_level2_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    n: ExprId,
    hi: ExprId,
    hj: ExprId,
    hk: ExprId,
) -> ExprId {
    let level3 = t_level3(d, i, j, k);
    let level3_lt = t_level3_lt(d, p, i, j, k, n, hi, hk);
    let cond = d.ble(k, i);
    bool_select_nat_lt(d, p, cond, j, level3, n, hj, level3_lt)
}

#[allow(clippy::too_many_arguments)]
fn transposition_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    n: ExprId,
    hi: ExprId,
    hj: ExprId,
    hk: ExprId,
) -> ExprId {
    let level2 = t_level2(d, i, j, k);
    let level2_lt = t_level2_lt(d, p, i, j, k, n, hi, hj, hk);
    let sk = d.succ(k);
    let cond = d.ble(sk, i);
    bool_select_nat_lt(d, p, cond, k, level2, n, hk, level2_lt)
}

/// `Nat.transposition_maps_into : ∀ i j n, Lt i j → Lt j n →
///   MapsInto (fun k => transposition i j k) n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_transposition_maps_into(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let h_ij_ty = d.lt(i, j);
    let hij_fv = d.fresh_fvar();
    let h_ij = d.kernel().fvar(hij_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_jn_ty = d.lt(j, n);
    let hjn_fv = d.fresh_fvar();
    let h_jn = d.kernel().fvar(hjn_fv);

    let sigma = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.transposition, &[i, j, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let concl = d.const_app(p.maps_into, &[sigma, n]);

    let le_i_j = le_of_lt(d, &p, i, j, h_ij);
    let hi = d.lemma(p.lt_of_le_of_lt, &[i, j, n, le_i_j, h_jn]);
    let hj = h_jn;

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let result = transposition_lt(d, &p, i, j, k, n, hi, hj, hk);

    let inner = d.lam_fv(hk_fv, hk_ty, result);
    let maps_into_proof = d.lam_fv(k_fv, nat, inner);

    let value = {
        let with_hjn = d.lam_fv(hjn_fv, h_jn_ty, maps_into_proof);
        let with_n = d.lam_fv(n_fv, nat, with_hjn);
        let with_hij = d.lam_fv(hij_fv, h_ij_ty, with_n);
        let with_j = d.lam_fv(j_fv, nat, with_hij);
        d.lam_fv(i_fv, nat, with_j)
    };
    let ty = {
        let with_hjn = d.arrow(h_jn_ty, concl);
        let with_n = d.pi_fv(n_fv, nat, with_hjn);
        let with_hij = d.arrow(h_ij_ty, with_n);
        let with_j = d.pi_fv(j_fv, nat, with_hij);
        d.pi_fv(i_fv, nat, with_j)
    };

    d.declare_theorem(p.transposition_maps_into, ty, value)
}

// ---------------------------------------------------------------------------
// `Nat.conjugate_injective` / `Nat.conjugate_maps_into` — generic over any
// involutive self-map `t`, not specialized to `Nat.transposition`.
// ---------------------------------------------------------------------------

/// `t (σ (t x))`, built directly (no lambda redex) for use as the value of
/// the conjugated function at `x`.
fn conjugate_at(d: &mut NatDev<'_>, t: ExprId, sigma: ExprId, x: ExprId) -> ExprId {
    let tx = d.apply(t, &[x]);
    let s_tx = d.apply(sigma, &[tx]);
    d.apply(t, &[s_tx])
}

/// `Nat.conjugate_injective : ∀ (t σ : Nat → Nat) (n : Nat),
///   (∀ x, Eq Nat (t (t x)) x) → MapsInto t n → InjectiveOn σ n →
///   InjectiveOn (fun k => t (σ (t k))) n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_conjugate_injective(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let t_inv_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let tx = d.apply(t, &[x]);
        let ttx = d.apply(t, &[tx]);
        let body = d.eq(ttx, x);
        d.pi_fv(x_fv, nat, body)
    };
    let tinv_fv = d.fresh_fvar();
    let t_inv = d.kernel().fvar(tinv_fv);

    let t_maps_ty = d.const_app(p.maps_into, &[t, n]);
    let tmaps_fv = d.fresh_fvar();
    let h_t_maps = d.kernel().fvar(tmaps_fv);

    let sigma_inj_ty = d.const_app(p.injective_on, &[sigma, n]);
    let sinj_fv = d.fresh_fvar();
    let h_sigma_inj = d.kernel().fvar(sinj_fv);

    let composed = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = conjugate_at(d, t, sigma, k);
        d.lam_fv(k_fv, nat, body)
    };
    let concl = d.const_app(p.injective_on, &[composed, n]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let han_ty = d.lt(a, n);
    let han_fv = d.fresh_fvar();
    let han = d.kernel().fvar(han_fv);
    let hbn_ty = d.lt(b, n);
    let hbn_fv = d.fresh_fvar();
    let hbn = d.kernel().fvar(hbn_fv);

    let comp_a = conjugate_at(d, t, sigma, a);
    let comp_b = conjugate_at(d, t, sigma, b);
    let heq_ty = d.eq(comp_a, comp_b);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let ta = d.apply(t, &[a]);
    let tb = d.apply(t, &[b]);
    let ta_lt_n = d.apply(h_t_maps, &[a, han]);
    let tb_lt_n = d.apply(h_t_maps, &[b, hbn]);

    let s_ta = d.apply(sigma, &[ta]);
    let s_tb = d.apply(sigma, &[tb]);
    // heq : t (sigma (t a)) = t (sigma (t b)), i.e. Eq Nat (t s_ta) (t s_tb).
    let step1 = injective_of_involutive(d, t, t_inv, s_ta, s_tb, heq);
    // step1 : sigma (t a) = sigma (t b); sigma injective on n at (t a, t b).
    let step2 = d.apply(h_sigma_inj, &[ta, tb, ta_lt_n, tb_lt_n, step1]);
    // step2 : t a = t b; cancel the involution once more.
    let final_proof = injective_of_involutive(d, t, t_inv, a, b, step2);

    let inner = d.lam_fv(heq_fv, heq_ty, final_proof);
    let with_hbn = d.lam_fv(hbn_fv, hbn_ty, inner);
    let with_han = d.lam_fv(han_fv, han_ty, with_hbn);
    let with_b = d.lam_fv(b_fv, nat, with_han);
    let with_a = d.lam_fv(a_fv, nat, with_b);

    let value = {
        let with_sinj = d.lam_fv(sinj_fv, sigma_inj_ty, with_a);
        let with_tmaps = d.lam_fv(tmaps_fv, t_maps_ty, with_sinj);
        let with_tinv = d.lam_fv(tinv_fv, t_inv_ty, with_tmaps);
        let with_n = d.lam_fv(n_fv, nat, with_tinv);
        let with_sigma = d.lam_fv(sigma_fv, fn_ty, with_n);
        d.lam_fv(t_fv, fn_ty, with_sigma)
    };
    let ty = {
        let with_sinj = d.arrow(sigma_inj_ty, concl);
        let with_tmaps = d.arrow(t_maps_ty, with_sinj);
        let with_tinv = d.arrow(t_inv_ty, with_tmaps);
        let with_n = d.pi_fv(n_fv, nat, with_tinv);
        let with_sigma = d.pi_fv(sigma_fv, fn_ty, with_n);
        d.pi_fv(t_fv, fn_ty, with_sigma)
    };

    d.declare_theorem(p.conjugate_injective, ty, value)
}

/// `Nat.conjugate_maps_into : ∀ (t σ : Nat → Nat) (n : Nat),
///   MapsInto t n → MapsInto σ n → MapsInto (fun k => t (σ (t k))) n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_conjugate_maps_into(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let t_maps_ty = d.const_app(p.maps_into, &[t, n]);
    let tmaps_fv = d.fresh_fvar();
    let h_t_maps = d.kernel().fvar(tmaps_fv);

    let sigma_maps_ty = d.const_app(p.maps_into, &[sigma, n]);
    let smaps_fv = d.fresh_fvar();
    let h_sigma_maps = d.kernel().fvar(smaps_fv);

    let composed = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = conjugate_at(d, t, sigma, k);
        d.lam_fv(k_fv, nat, body)
    };
    let concl = d.const_app(p.maps_into, &[composed, n]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let tk = d.apply(t, &[k]);
    let tk_lt_n = d.apply(h_t_maps, &[k, hk]);
    let s_tk = d.apply(sigma, &[tk]);
    let s_tk_lt_n = d.apply(h_sigma_maps, &[tk, tk_lt_n]);
    let t_s_tk_lt_n = d.apply(h_t_maps, &[s_tk, s_tk_lt_n]);

    let inner = d.lam_fv(hk_fv, hk_ty, t_s_tk_lt_n);
    let maps_proof = d.lam_fv(k_fv, nat, inner);

    let value = {
        let with_smaps = d.lam_fv(smaps_fv, sigma_maps_ty, maps_proof);
        let with_tmaps = d.lam_fv(tmaps_fv, t_maps_ty, with_smaps);
        let with_n = d.lam_fv(n_fv, nat, with_tmaps);
        let with_sigma = d.lam_fv(sigma_fv, fn_ty, with_n);
        d.lam_fv(t_fv, fn_ty, with_sigma)
    };
    let ty = {
        let with_smaps = d.arrow(sigma_maps_ty, concl);
        let with_tmaps = d.arrow(t_maps_ty, with_smaps);
        let with_n = d.pi_fv(n_fv, nat, with_tmaps);
        let with_sigma = d.pi_fv(sigma_fv, fn_ty, with_n);
        d.pi_fv(t_fv, fn_ty, with_sigma)
    };

    d.declare_theorem(p.conjugate_maps_into, ty, value)
}

// ---------------------------------------------------------------------------
// The pointwise correctness facts as KERNEL THEOREMS (ADR-1470's remainder)
// ---------------------------------------------------------------------------
//
// `transposition_eq_at_i`/`_at_j`/`_gt_j`/`_between`/`_lt_i` above are Rust
// helpers taking `&mut NatDev<'_>`, so they are unreachable from any prelude
// built on a different dev struct -- `rat_prelude` runs on `IntDev`, and Rust
// does not let a function written against one concrete type be called with a
// value of another even when both implement `NatOps`. ADR-1470 recorded that
// wall as the reason its selection-lemma route could not reuse
// `Nat.transposition`, and sketched a second, private two-point swap instead.
//
// A `NameId` has no such restriction, so the four facts a caller in another
// prelude actually needs are declared here as theorems instead, stated at the
// `Nat.transposition` CONSTANT (the helpers above build the raw case tree; the
// two are defeq by delta, so each helper serves directly as the proof body).
// `transposition_eq_of_ne` is the one that is not a helper already: it is the
// five-region split `declare_transposition_involutive` runs, with the two
// equality regions discharged by the `Not` hypotheses instead of transported.

/// `False.rec` into `goal` from a proof of `False`. Per-file local copy of the
/// `absurd` convention used elsewhere in `nat_prelude`.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, goal: ExprId, contradiction: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d
        .kernel()
        .lam(anon, false_ty, goal, crate::BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, contradiction])
}

/// Admit `Nat.transposition_at_i : ∀ i j, Eq Nat (transposition i j i) j` —
/// unconditional, because the `i` leaf of the case tree is reached without any
/// ordering fact.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_transposition_at_i(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let lhs = d.const_app(p.transposition, &[i, j, i]);
    let goal = d.eq(lhs, j);
    let body = transposition_eq_at_i(d, &p, i, j);

    let ty = {
        let with_j = d.pi_fv(j_fv, nat, goal);
        d.pi_fv(i_fv, nat, with_j)
    };
    let value = {
        let with_j = d.lam_fv(j_fv, nat, body);
        d.lam_fv(i_fv, nat, with_j)
    };
    d.declare_theorem(p.transposition_at_i, ty, value)
}

/// Admit `Nat.transposition_at_j : ∀ i j, Lt i j →
/// Eq Nat (transposition i j j) i`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_transposition_at_j(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let h_ij_ty = d.lt(i, j);
    let hij_fv = d.fresh_fvar();
    let h_ij = d.kernel().fvar(hij_fv);

    let lhs = d.const_app(p.transposition, &[i, j, j]);
    let goal = d.eq(lhs, i);
    let body = transposition_eq_at_j(d, &p, i, j, h_ij);

    let ty = {
        let with_h = d.arrow(h_ij_ty, goal);
        let with_j = d.pi_fv(j_fv, nat, with_h);
        d.pi_fv(i_fv, nat, with_j)
    };
    let value = {
        let with_h = d.lam_fv(hij_fv, h_ij_ty, body);
        let with_j = d.lam_fv(j_fv, nat, with_h);
        d.lam_fv(i_fv, nat, with_j)
    };
    d.declare_theorem(p.transposition_at_j, ty, value)
}

/// Admit `Nat.transposition_gt_j : ∀ i j k, Lt i j → Lt j k →
/// Eq Nat (transposition i j k) k` — the region above both swapped points,
/// the one a cursor induction needs in order to know it has not disturbed
/// anything it already fixed.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_transposition_gt_j(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ij_ty = d.lt(i, j);
    let hij_fv = d.fresh_fvar();
    let h_ij = d.kernel().fvar(hij_fv);
    let h_jk_ty = d.lt(j, k);
    let hjk_fv = d.fresh_fvar();
    let h_jk = d.kernel().fvar(hjk_fv);

    let lhs = d.const_app(p.transposition, &[i, j, k]);
    let goal = d.eq(lhs, k);
    let body = transposition_eq_gt_j(d, &p, i, j, k, h_ij, h_jk);

    let ty = {
        let with_h2 = d.arrow(h_jk_ty, goal);
        let with_h1 = d.arrow(h_ij_ty, with_h2);
        let with_k = d.pi_fv(k_fv, nat, with_h1);
        let with_j = d.pi_fv(j_fv, nat, with_k);
        d.pi_fv(i_fv, nat, with_j)
    };
    let value = {
        let with_h2 = d.lam_fv(hjk_fv, h_jk_ty, body);
        let with_h1 = d.lam_fv(hij_fv, h_ij_ty, with_h2);
        let with_k = d.lam_fv(k_fv, nat, with_h1);
        let with_j = d.lam_fv(j_fv, nat, with_k);
        d.lam_fv(i_fv, nat, with_j)
    };
    d.declare_theorem(p.transposition_gt_j, ty, value)
}

/// Admit `Nat.transposition_eq_of_ne : ∀ i j k, Lt i j → Not (Eq Nat k i) →
/// Not (Eq Nat k j) → Eq Nat (transposition i j k) k` — a transposition fixes
/// every point that is neither of the two it exchanges.
///
/// The same five-region split as [`declare_transposition_involutive`] (nested
/// [`trichotomy`], `i` against `k` then `j` against `k`), with the three
/// inequality regions closed by [`transposition_eq_lt_i`],
/// [`transposition_eq_between`] and [`transposition_eq_gt_j`] and the two
/// equality regions discharged by the corresponding `Not` hypothesis through
/// [`ex_falso`] rather than transported.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_transposition_eq_of_ne(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let h_ij_ty = d.lt(i, j);
    let hij_fv = d.fresh_fvar();
    let h_ij = d.kernel().fvar(hij_fv);

    let eq_k_i = d.eq(k, i);
    let not_ki_ty = d.const_app(p.logic.not, &[eq_k_i]);
    let hni_fv = d.fresh_fvar();
    let hni = d.kernel().fvar(hni_fv);

    let eq_k_j = d.eq(k, j);
    let not_kj_ty = d.const_app(p.logic.not, &[eq_k_j]);
    let hnj_fv = d.fresh_fvar();
    let hnj = d.kernel().fvar(hnj_fv);

    let lhs = d.const_app(p.transposition, &[i, j, k]);
    let goal = d.eq(lhs, k);

    let lt_k_i = d.lt(k, i);
    let lt_i_k = d.lt(i, k);
    let lt_k_j = d.lt(k, j);
    let lt_j_k = d.lt(j, k);

    // --- region: k < i ---
    let branch_lt_i = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let fact = transposition_eq_lt_i(d, &p, i, j, k, h);
        d.lam_fv(h_fv, lt_k_i, fact)
    };

    // --- region: k = i, refuted by the first `Not` ---
    let branch_eq_i = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let contradiction = d.apply(hni, &[h]);
        let body = ex_falso(d, &p, goal, contradiction);
        d.lam_fv(h_fv, eq_k_i, body)
    };

    // --- region: i < k, split against j ---
    let branch_gt_i = {
        let hg_fv = d.fresh_fvar();
        let hg = d.kernel().fvar(hg_fv);

        let tri_inner = trichotomy(d, &p, j, k);

        let inner_lt_j = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let fact = transposition_eq_between(d, &p, i, j, k, hg, h2);
            d.lam_fv(h2_fv, lt_k_j, fact)
        };

        let inner_rest = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let inner_eq_j = {
                let h3_fv = d.fresh_fvar();
                let h3 = d.kernel().fvar(h3_fv);
                let contradiction = d.apply(hnj, &[h3]);
                let body = ex_falso(d, &p, goal, contradiction);
                d.lam_fv(h3_fv, eq_k_j, body)
            };
            let inner_gt_j = {
                let h3_fv = d.fresh_fvar();
                let h3 = d.kernel().fvar(h3_fv);
                let fact = transposition_eq_gt_j(d, &p, i, j, k, h_ij, h3);
                d.lam_fv(h3_fv, lt_j_k, fact)
            };

            let body = d.const_app(
                p.logic.or_elim,
                &[eq_k_j, lt_j_k, goal, h2, inner_eq_j, inner_gt_j],
            );
            let or_rest2_ty = d.const_app(p.logic.or, &[eq_k_j, lt_j_k]);
            d.lam_fv(h2_fv, or_rest2_ty, body)
        };

        let or_rest2_ty = d.const_app(p.logic.or, &[eq_k_j, lt_j_k]);
        let body = d.const_app(
            p.logic.or_elim,
            &[lt_k_j, or_rest2_ty, goal, tri_inner, inner_lt_j, inner_rest],
        );
        d.lam_fv(hg_fv, lt_i_k, body)
    };

    let branch_rest = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.const_app(
            p.logic.or_elim,
            &[eq_k_i, lt_i_k, goal, h, branch_eq_i, branch_gt_i],
        );
        let or_rest_ty = d.const_app(p.logic.or, &[eq_k_i, lt_i_k]);
        d.lam_fv(h_fv, or_rest_ty, body)
    };

    let tri_outer = trichotomy(d, &p, i, k);
    let or_rest_ty = d.const_app(p.logic.or, &[eq_k_i, lt_i_k]);
    let proof_body = d.const_app(
        p.logic.or_elim,
        &[
            lt_k_i,
            or_rest_ty,
            goal,
            tri_outer,
            branch_lt_i,
            branch_rest,
        ],
    );

    let ty = {
        let with_nj = d.arrow(not_kj_ty, goal);
        let with_ni = d.arrow(not_ki_ty, with_nj);
        let with_hij = d.arrow(h_ij_ty, with_ni);
        let with_k = d.pi_fv(k_fv, nat, with_hij);
        let with_j = d.pi_fv(j_fv, nat, with_k);
        d.pi_fv(i_fv, nat, with_j)
    };
    let value = {
        let with_nj = d.lam_fv(hnj_fv, not_kj_ty, proof_body);
        let with_ni = d.lam_fv(hni_fv, not_ki_ty, with_nj);
        let with_hij = d.lam_fv(hij_fv, h_ij_ty, with_ni);
        let with_k = d.lam_fv(k_fv, nat, with_hij);
        let with_j = d.lam_fv(j_fv, nat, with_k);
        d.lam_fv(i_fv, nat, with_j)
    };
    d.declare_theorem(p.transposition_eq_of_ne, ty, value)
}
