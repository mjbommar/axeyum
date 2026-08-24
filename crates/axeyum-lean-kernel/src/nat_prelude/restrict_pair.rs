//! `Nat.restrict_pair_injective` / `Nat.restrict_pair_maps_into` — "a
//! bijection of `[0,n)` fixing a two-element subset `{i,j}` setwise
//! restricts to a bijection of the complement" — the `N → N−2` step
//! `wilson.rs`'s interior collapse needs (module doc, "What Wilson is
//! blocked on now", item 4(b)). `Nat.restrict_injective`/`restrict_maps_into`
//! (`finite.rs`) remove exactly one TOP index via override; this removes an
//! arbitrary interior PAIR `{i,j}` via index-shift/compaction, and is built
//! from scratch rather than adapted from them.
//!
//! ## The restriction map
//!
//! Built in two independently-named pieces, mirroring `finite.rs`'s own
//! `point_override`/`compact` split into an "insert" direction and a
//! "remove" direction:
//!
//! - [`expand_pair`] `i j k` sends `[0, n−2)` into the complement of `{i,j}`
//!   inside `[0, n)`: `k` if `k < i`; `succ k` if `i ≤ k` and `k+2 ≤ j`;
//!   `succ (succ k)` otherwise. Purely additive (`succ`, `Nat.ble` cuts) —
//!   **no `Nat.sub`/`Nat.pred`** — matching `transposition`'s and
//!   `point_override`'s own cascaded-`Nat.ble` convention. (Three lanes were
//!   bitten by truncated `Nat.sub` earlier the same day; this sidesteps it
//!   entirely by comparing `k`, `k+1`, `k+2` directly against `i`/`j` instead
//!   of comparing shifted/subtracted quantities.)
//! - [`compact_pair`] `i j x := compact (pred j) (compact i x)` — the
//!   INVERSE direction, reusing `finite.rs`'s already-proved single-point
//!   `compact`/`compact_eq_of_le`/`compact_eq_of_gt`/`compact_injective`
//!   TWICE (removing `i`, then removing `j`'s own image under that removal,
//!   which is `pred j` since `i < j` compacts `j` to `pred j`). This is the
//!   one place `Nat.pred` appears, and only ever applied to a value already
//!   known positive (`i < j` gives `j`, and later `i < x`/`j < x` give `x`,
//!   both `> 0`), via the same `pos_implies_succ_pred` route `finite.rs`'s
//!   own `compact_lt_of` already uses for exactly this reason.
//!
//! [`expand_compact_pair_id`] proves `compact_pair` is a **left inverse** of
//! `expand_pair` on `[0,n)` — an identity independent of any domain bound
//! (`expand_pair`/`compact_pair` never reference `n`), used only to close the
//! last step of injectivity (`expand_pair i j a = expand_pair i j b ⊢ a = b`)
//! without a second, independent injectivity argument for `expand_pair`
//! itself.
//!
//! ## "Fixes `{i,j}` setwise": the pointwise form
//!
//! [`Nat.setwise_fixed`](super::NatPrelude::setwise_fixed) `σ i j := And (Eq
//! Nat (σ i) i) (Eq Nat (σ j) j)` — **pointwise**, not the disjunctive "swaps
//! or fixes" reading. `Int.inverseIndex_fixed_point` (`int_prelude/wilson.rs`)
//! gives Wilson's own two exceptional indices (`0`, `p−2`) exactly this way —
//! each is individually a fixed point, not merely swapped with the other —
//! so the pointwise form is what the interior-collapse application actually
//! has on hand, and the weaker predicate is exactly the one that transports.
//!
//! ## The headline theorems
//!
//! `Nat.restrict_pair_injective`/`Nat.restrict_pair_maps_into`: given `σ`
//! `InjectiveOn`/`MapsInto` on `succ (succ n)`, `i < j < succ (succ n)`, and
//! `setwise_fixed σ i j`, the induced map `fun k => compact_pair i j (σ
//! (expand_pair i j k))` is `InjectiveOn`/`MapsInto` on `n`. Injectivity
//! needs no `MapsInto` hypothesis at all (mirroring `restrict_injective`'s
//! own omission of it) — every bound `compact_injective`'s two applications
//! need comes from `expand_pair`'s own additive bound
//! ([`expand_pair_lt_bound`]) and the hypotheses already in scope, never from
//! `σ`'s codomain. `MapsInto` reuses `finite.rs`'s `compact_lt_of` TWICE, the
//! same composition trick `compact_pair`'s own value lemmas use.
//!
//! Both theorems establish `expand_pair i j k ≠ i` and `≠ j` **unconditionally**
//! (any `k`, given only `i < j`: [`expand_pair_ne_i`]/[`expand_pair_ne_j`]),
//! then transport that through `σ`'s injectivity plus `setwise_fixed` to get
//! `σ (expand_pair i j k) ≠ i, j` ([`ne_of_sigma_apply`]) — the fact
//! `compact_pair`'s own case analysis ([`compact_pair_off`]) needs to know
//! which of `compact_pair`'s three regions a value falls into.

use super::NatPrelude;
use super::finite::{
    compact, compact_eq_of_gt, compact_eq_of_le, compact_injective, compact_lt_of, le_of_lt,
    ne_of_lt, ne_symm, pos_implies_succ_pred, restrict_ble_eq_false_of_lt, select_nat_false,
    select_nat_true, trichotomy, two_way_split, zero_lt_via_c,
};
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// `Nat.setwise_fixed` — the pointwise predicate (module doc above).
// ---------------------------------------------------------------------------

/// Declare `Nat.setwise_fixed σ i j := And (Eq Nat (σ i) i) (Eq Nat (σ j) j)`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_setwise_fixed(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();

    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let sigma_i = d.apply(sigma, &[i]);
    let sigma_j = d.apply(sigma, &[j]);
    let fix_i = d.eq(sigma_i, i);
    let fix_j = d.eq(sigma_j, j);
    let body = d.const_app(p.logic.and, &[fix_i, fix_j]);

    let value = {
        let with_j = d.lam_fv(j_fv, nat, body);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        d.lam_fv(sigma_fv, fn_ty, with_i)
    };
    let ty = {
        let over_j = d.arrow(nat, prop);
        let over_i = d.arrow(nat, over_j);
        d.arrow(fn_ty, over_i)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.setwise_fixed,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

// ---------------------------------------------------------------------------
// `expand_pair` — the restriction map, task 1. Private: reused inside the
// two headline theorems' conclusion lambdas the same way `point_override`
// and `compact` are, never declared as a public `Nat.*` definition.
// ---------------------------------------------------------------------------

/// `expand_pair i j k`'s value: `k` if `k < i`; `succ k` if `i ≤ k` and
/// `k + 2 ≤ j`; `succ (succ k)` otherwise. Three nested `Nat.ble` cuts on
/// `succ k` and `succ (succ k)` directly against `i`/`j` — additive, no
/// `Nat.sub`.
fn expand_pair(d: &mut NatDev<'_>, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    let below_i = d.ble(succ_k, i);
    let succ2_k = d.succ(succ_k);
    let below_j = d.ble(succ2_k, j);
    let inner = d.bool_select_nat(below_j, succ_k, succ2_k);
    d.bool_select_nat(below_i, k, inner)
}

/// `h : Lt k i ⊢ Eq Nat (expand_pair i j k) k`.
fn expand_eq_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let succ_k = d.succ(k);
    let below_i = d.ble(succ_k, i);
    let succ2_k = d.succ(succ_k);
    let below_j = d.ble(succ2_k, j);
    let inner = d.bool_select_nat(below_j, succ_k, succ2_k);
    let below_i_true = d.lemma(p.ble_eq_true_of_le, &[succ_k, i, h]);
    select_nat_true(d, below_i, k, inner, below_i_true)
}

/// `h1 : Le i k, h2 : Le (succ (succ k)) j ⊢
///   Eq Nat (expand_pair i j k) (succ k)`.
fn expand_eq_mid(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let p = *p;
    let succ_k = d.succ(k);
    let below_i = d.ble(succ_k, i);
    let succ2_k = d.succ(succ_k);
    let below_j = d.ble(succ2_k, j);
    let inner = d.bool_select_nat(below_j, succ_k, succ2_k);

    let h1_succ = d.lemma(p.le_succ_succ, &[i, k, h1]); // Lt i succ_k
    let below_i_false = restrict_ble_eq_false_of_lt(d, &p, succ_k, i, h1_succ);
    let step1 = select_nat_false(d, below_i, k, inner, below_i_false);

    let below_j_true = d.lemma(p.ble_eq_true_of_le, &[succ2_k, j, h2]);
    let step2 = select_nat_true(d, below_j, succ_k, succ2_k, below_j_true);

    let start = expand_pair(d, i, j, k);
    d.trans(start, inner, succ_k, step1, step2)
}

/// `h1 : Le i k, h2 : Lt j (succ (succ k)) ⊢
///   Eq Nat (expand_pair i j k) (succ (succ k))`.
fn expand_eq_hi(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let p = *p;
    let succ_k = d.succ(k);
    let below_i = d.ble(succ_k, i);
    let succ2_k = d.succ(succ_k);
    let below_j = d.ble(succ2_k, j);
    let inner = d.bool_select_nat(below_j, succ_k, succ2_k);

    let h1_succ = d.lemma(p.le_succ_succ, &[i, k, h1]);
    let below_i_false = restrict_ble_eq_false_of_lt(d, &p, succ_k, i, h1_succ);
    let step1 = select_nat_false(d, below_i, k, inner, below_i_false);

    let below_j_false = restrict_ble_eq_false_of_lt(d, &p, succ2_k, j, h2);
    let step2 = select_nat_false(d, below_j, succ_k, succ2_k, below_j_false);

    let start = expand_pair(d, i, j, k);
    d.trans(start, inner, succ2_k, step1, step2)
}

/// Case-split `k` against `i` and `j` — `Lt k i`, or `Le i k` further split
/// by `Le (succ (succ k)) j` vs `Lt j (succ (succ k))` — reusing
/// `Nat.lt_or_ge` for both splits (never `Nat.beq`), routing each region
/// through the matching continuation. All three continuations must target
/// the same `goal`.
#[allow(clippy::too_many_arguments)]
fn expand_pair_cases(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    goal: ExprId,
    on_lt: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    on_mid: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
    on_hi: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let succ_k = d.succ(k);
    let succ2_k = d.succ(succ_k);

    let split1 = d.lemma(p.lt_or_ge, &[k, i]); // Or (Lt k i) (Le i k)
    let lt_ki = d.lt(k, i);
    let le_ik = d.le(i, k);

    let branch_lt = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = on_lt(d, h);
        d.lam_fv(h_fv, lt_ki, body)
    };
    let branch_rest = {
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);

        let split2 = d.lemma(p.lt_or_ge, &[j, succ2_k]); // Or (Lt j succ2_k) (Le succ2_k j)
        let lt_j_s2k = d.lt(j, succ2_k);
        let le_s2k_j = d.le(succ2_k, j);

        let sub_hi = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let body = on_hi(d, h1, h2);
            d.lam_fv(h2_fv, lt_j_s2k, body)
        };
        let sub_mid = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let body = on_mid(d, h1, h2);
            d.lam_fv(h2_fv, le_s2k_j, body)
        };
        let body = d.const_app(
            logic.or_elim,
            &[lt_j_s2k, le_s2k_j, goal, split2, sub_hi, sub_mid],
        );
        d.lam_fv(h1_fv, le_ik, body)
    };
    d.const_app(
        logic.or_elim,
        &[lt_ki, le_ik, goal, split1, branch_lt, branch_rest],
    )
}

/// `Not (Eq Nat z c)` as a plain arrow type `Eq Nat z c → False`.
fn not_eq_ty(d: &mut NatDev<'_>, p: &NatPrelude, z: ExprId, c: ExprId) -> ExprId {
    let eqzc = d.eq(z, c);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    d.arrow(eqzc, false_ty)
}

/// `Not (Eq Nat (expand_pair i j k) i)` — unconditional (any `k`, given only
/// `i < j`): each region's value (`k`, `succ k`, `succ (succ k)`) is
/// provably `< i` or `> i`, so never equal to `i`.
fn expand_pair_ne_i(d: &mut NatDev<'_>, p: &NatPrelude, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let p = *p;
    let ek = expand_pair(d, i, j, k);
    let goal = not_eq_ty(d, &p, ek, i);

    expand_pair_cases(
        d,
        &p,
        i,
        j,
        k,
        goal,
        &|d, h| {
            let eq_ek_k = expand_eq_lt(d, &p, i, j, k, h);
            let ne_k_i = ne_of_lt(d, &p, k, i, h);
            let eq_k_ek = d.symm(ek, k, eq_ek_k);
            let motive = d.eq_motive(k, &|d, z| not_eq_ty(d, &p, z, i));
            d.transport(k, motive, ne_k_i, ek, eq_k_ek)
        },
        &|d, h1, h2| {
            let succ_k = d.succ(k);
            let eq_ek_sk = expand_eq_mid(d, &p, i, j, k, h1, h2);
            let lt_i_succk = d.lemma(p.lt_succ_of_le, &[i, k, h1]);
            let ne_i_sk = ne_of_lt(d, &p, i, succ_k, lt_i_succk);
            let ne_sk_i = ne_symm(d, i, succ_k, ne_i_sk);
            let eq_sk_ek = d.symm(ek, succ_k, eq_ek_sk);
            let motive = d.eq_motive(succ_k, &|d, z| not_eq_ty(d, &p, z, i));
            d.transport(succ_k, motive, ne_sk_i, ek, eq_sk_ek)
        },
        &|d, h1, h2| {
            let succ_k = d.succ(k);
            let succ2_k = d.succ(succ_k);
            let eq_ek_s2k = expand_eq_hi(d, &p, i, j, k, h1, h2);
            let le_i_succk = d.lemma(p.le_succ_of_le, &[i, k, h1]);
            let lt_i_succ2k = d.lemma(p.lt_succ_of_le, &[i, succ_k, le_i_succk]);
            let ne_i_s2k = ne_of_lt(d, &p, i, succ2_k, lt_i_succ2k);
            let ne_s2k_i = ne_symm(d, i, succ2_k, ne_i_s2k);
            let eq_s2k_ek = d.symm(ek, succ2_k, eq_ek_s2k);
            let motive = d.eq_motive(succ2_k, &|d, z| not_eq_ty(d, &p, z, i));
            d.transport(succ2_k, motive, ne_s2k_i, ek, eq_s2k_ek)
        },
    )
}

/// `Not (Eq Nat (expand_pair i j k) j)` — unconditional given `Lt i j`.
fn expand_pair_ne_j(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    hij: ExprId,
) -> ExprId {
    let p = *p;
    let ek = expand_pair(d, i, j, k);
    let goal = not_eq_ty(d, &p, ek, j);

    expand_pair_cases(
        d,
        &p,
        i,
        j,
        k,
        goal,
        &|d, h| {
            let eq_ek_k = expand_eq_lt(d, &p, i, j, k, h);
            let i_le_j = le_of_lt(d, &p, i, j, hij);
            let k_lt_j = d.lemma(p.lt_of_lt_of_le, &[k, i, j, h, i_le_j]);
            let ne_k_j = ne_of_lt(d, &p, k, j, k_lt_j);
            let eq_k_ek = d.symm(ek, k, eq_ek_k);
            let motive = d.eq_motive(k, &|d, z| not_eq_ty(d, &p, z, j));
            d.transport(k, motive, ne_k_j, ek, eq_k_ek)
        },
        &|d, h1, h2| {
            // h2 : Le (succ (succ k)) j, definitionally Lt (succ k) j.
            let succ_k = d.succ(k);
            let eq_ek_sk = expand_eq_mid(d, &p, i, j, k, h1, h2);
            let ne_sk_j = ne_of_lt(d, &p, succ_k, j, h2);
            let eq_sk_ek = d.symm(ek, succ_k, eq_ek_sk);
            let motive = d.eq_motive(succ_k, &|d, z| not_eq_ty(d, &p, z, j));
            d.transport(succ_k, motive, ne_sk_j, ek, eq_sk_ek)
        },
        &|d, h1, h2| {
            let succ_k = d.succ(k);
            let succ2_k = d.succ(succ_k);
            let eq_ek_s2k = expand_eq_hi(d, &p, i, j, k, h1, h2);
            let ne_j_s2k = ne_of_lt(d, &p, j, succ2_k, h2);
            let ne_s2k_j = ne_symm(d, j, succ2_k, ne_j_s2k);
            let eq_s2k_ek = d.symm(ek, succ2_k, eq_ek_s2k);
            let motive = d.eq_motive(succ2_k, &|d, z| not_eq_ty(d, &p, z, j));
            d.transport(succ2_k, motive, ne_s2k_j, ek, eq_s2k_ek)
        },
    )
}

/// `hjn : Lt j (succ (succ n)), hk : Lt k n ⊢
///   Lt (expand_pair i j k) (succ (succ n))`.
#[allow(clippy::too_many_arguments)]
fn expand_pair_lt_bound(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    n: ExprId,
    k: ExprId,
    hjn: ExprId,
    hk: ExprId,
) -> ExprId {
    let p = *p;
    let ek = expand_pair(d, i, j, k);
    let sn = d.succ(n);
    let ssn = d.succ(sn);
    let goal = d.lt(ek, ssn);

    expand_pair_cases(
        d,
        &p,
        i,
        j,
        k,
        goal,
        &|d, h| {
            let eq_ek_k = expand_eq_lt(d, &p, i, j, k, h);
            let n_le_sn = d.lemma(p.le_succ, &[n]);
            let sn_le_ssn = d.lemma(p.le_succ, &[sn]);
            let n_le_ssn = d.lemma(p.le_trans, &[n, sn, ssn, n_le_sn, sn_le_ssn]);
            let k_lt_ssn = d.lemma(p.lt_of_lt_of_le, &[k, n, ssn, hk, n_le_ssn]);
            let eq_k_ek = d.symm(ek, k, eq_ek_k);
            let motive = d.eq_motive(k, &|d, z| d.lt(z, ssn));
            d.transport(k, motive, k_lt_ssn, ek, eq_k_ek)
        },
        &|d, h1, h2| {
            let succ_k = d.succ(k);
            let succ2_k = d.succ(succ_k);
            let eq_ek_sk = expand_eq_mid(d, &p, i, j, k, h1, h2);
            let s2k_lt_ssn = d.lemma(p.lt_of_le_of_lt, &[succ2_k, j, ssn, h2, hjn]);
            let sk_le_s2k = d.lemma(p.le_succ, &[succ_k]);
            let sk_lt_ssn = d.lemma(
                p.lt_of_le_of_lt,
                &[succ_k, succ2_k, ssn, sk_le_s2k, s2k_lt_ssn],
            );
            let eq_sk_ek = d.symm(ek, succ_k, eq_ek_sk);
            let motive = d.eq_motive(succ_k, &|d, z| d.lt(z, ssn));
            d.transport(succ_k, motive, sk_lt_ssn, ek, eq_sk_ek)
        },
        &|d, h1, h2| {
            let succ_k = d.succ(k);
            let succ2_k = d.succ(succ_k);
            let eq_ek_s2k = expand_eq_hi(d, &p, i, j, k, h1, h2);
            let step1 = d.lemma(p.le_succ_succ, &[succ_k, n, hk]); // Le succ2_k sn
            let step2 = d.lemma(p.le_succ_succ, &[succ2_k, sn, step1]); // Lt succ2_k ssn
            let eq_s2k_ek = d.symm(ek, succ2_k, eq_ek_s2k);
            let motive = d.eq_motive(succ2_k, &|d, z| d.lt(z, ssn));
            d.transport(succ2_k, motive, step2, ek, eq_s2k_ek)
        },
    )
}

// ---------------------------------------------------------------------------
// `compact_pair` — the inverse direction, composed from `finite.rs`'s
// already-proved single-point `compact`.
// ---------------------------------------------------------------------------

/// `compact_pair i j x := compact (pred j) (compact i x)` — compact around
/// `i` first, then around `j`'s own image under that compaction (`pred j`,
/// since `i < j` compacts `j` itself to `pred j` via `compact_eq_of_gt`).
fn compact_pair(d: &mut NatDev<'_>, i: ExprId, j: ExprId, x: ExprId) -> ExprId {
    let pj = d.pred(j);
    let cix = compact(d, i, x);
    compact(d, pj, cix)
}

/// `hij : Lt i j ⊢ Le i (pred j)` — `j` is positive (`i < j`, `i ≥ 0`), so
/// `j = succ (pred j)`; substituting that into `hij`'s underlying
/// `Le (succ i) j` and stripping the shared successor gives the
/// predecessor-shifted bound.
fn i_le_pred_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    hij: ExprId,
) -> ExprId {
    let p = *p;
    let pos_j = zero_lt_via_c(d, &p, i, j, hij);
    let j_eq = {
        let f = pos_implies_succ_pred(d, &p, j);
        d.apply(f, &[pos_j])
    }; // Eq j (succ (pred j))
    let pj = d.pred(j);
    let spj = d.succ(pj);
    let succ_i = d.succ(i);
    let motive = d.eq_motive(j, &|d, z| d.le(succ_i, z));
    let transported = d.transport(j, motive, hij, spj, j_eq); // Le succ_i spj
    d.lemma(p.le_of_succ_le_succ, &[i, pj, transported])
}

/// `ha : Lt zero a, h : Lt a b ⊢ Lt (pred a) (pred b)` — both `a` and `b` are
/// then positive (`b` transitively via `ha` and `h`), so each equals the
/// successor of its own predecessor; substituting both into `h`'s underlying
/// `Le (succ a) b` and stripping the shared successor once gives the
/// predecessor-shifted strict order fact.
fn pred_lt_pred_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let pa = d.pred(a);
    let pb = d.pred(b);
    let spa = d.succ(pa);
    let sspa = d.succ(spa);
    let spb = d.succ(pb);

    let a_eq = {
        let f = pos_implies_succ_pred(d, &p, a);
        d.apply(f, &[ha])
    }; // Eq a spa

    let le_zero_a = le_of_lt(d, &p, zero, a, ha);
    let pos_b = d.lemma(p.lt_of_le_of_lt, &[zero, a, b, le_zero_a, h]);
    let b_eq = {
        let f = pos_implies_succ_pred(d, &p, b);
        d.apply(f, &[pos_b])
    }; // Eq b spb

    // step1 : Le sspa b  (rewrite a -> spa inside h's type `Le (succ a) b`)
    let step1 = {
        let motive = d.eq_motive(a, &|d, z| {
            let sz = d.succ(z);
            d.le(sz, b)
        });
        d.transport(a, motive, h, spa, a_eq)
    };
    // step2 : Le sspa spb  (rewrite b -> spb inside step1's type)
    let step2 = {
        let motive = d.eq_motive(b, &|d, z| d.le(sspa, z));
        d.transport(b, motive, step1, spb, b_eq)
    };
    d.lemma(p.le_of_succ_le_succ, &[spa, pb, step2])
}

/// `hne : Not (Eq Nat x c) ⊢ Or (Lt x c) (Lt c x)` — `trichotomy`'s equality
/// leaf is impossible under `hne`.
fn off_from_ne(d: &mut NatDev<'_>, p: &NatPrelude, c: ExprId, x: ExprId, hne: ExprId) -> ExprId {
    let tri = trichotomy(d, p, c, x);
    two_way_split(d, p, c, x, tri, &|d, heq| d.apply(hne, &[heq]))
}

/// From `x ≠ i` and `x ≠ j` (`i < j` global), determine where `compact i x`
/// falls relative to `pred j` — the "off" hypothesis `compact_injective`/
/// `compact_lt_of` need for the OUTER application in `compact_pair`'s
/// composed proofs.
#[allow(clippy::too_many_arguments)]
fn compact_pair_off(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    x: ExprId,
    hij: ExprId,
    hne_i: ExprId,
    hne_j: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let cix = compact(d, i, x);
    let pj = d.pred(j);
    let lt_cix_pj = d.lt(cix, pj);
    let lt_pj_cix = d.lt(pj, cix);
    let target = d.const_app(logic.or, &[lt_cix_pj, lt_pj_cix]);

    let off_i = off_from_ne(d, &p, i, x, hne_i); // Or (Lt x i) (Lt i x)
    let lt_xi = d.lt(x, i);
    let lt_ix = d.lt(i, x);

    let on_lt_i = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv); // h : Lt x i
        let x_le_i = le_of_lt(d, &p, x, i, h);
        let eq_cix_x = compact_eq_of_le(d, &p, i, x, x_le_i); // Eq cix x
        let i_le_pj = i_le_pred_of_lt(d, &p, i, j, hij);
        let x_lt_pj = d.lemma(p.lt_of_lt_of_le, &[x, i, pj, h, i_le_pj]);
        let eq_x_cix = d.symm(cix, x, eq_cix_x);
        let motive = d.eq_motive(x, &|d, z| d.lt(z, pj));
        let result = d.transport(x, motive, x_lt_pj, cix, eq_x_cix); // Lt cix pj
        let body = d.const_app(logic.or_inl, &[lt_cix_pj, lt_pj_cix, result]);
        d.lam_fv(h_fv, lt_xi, body)
    };

    let on_gt_i = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv); // h : Lt i x
        let eq_cix_px = compact_eq_of_gt(d, &p, i, x, h); // Eq cix (pred x)
        let px = d.pred(x);
        let eq_px_cix = d.symm(cix, px, eq_cix_px);

        let off_j = off_from_ne(d, &p, j, x, hne_j); // Or (Lt x j) (Lt j x)
        let lt_xj = d.lt(x, j);
        let lt_jx = d.lt(j, x);

        let sub_lt_j = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv); // h2 : Lt x j
            let pos_x = zero_lt_via_c(d, &p, i, x, h);
            let px_lt_pj = pred_lt_pred_of_lt(d, &p, x, j, pos_x, h2); // Lt px pj
            let motive = d.eq_motive(px, &|d, z| d.lt(z, pj));
            let result = d.transport(px, motive, px_lt_pj, cix, eq_px_cix); // Lt cix pj
            let body = d.const_app(logic.or_inl, &[lt_cix_pj, lt_pj_cix, result]);
            d.lam_fv(h2_fv, lt_xj, body)
        };
        let sub_gt_j = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv); // h2 : Lt j x
            let pos_j = zero_lt_via_c(d, &p, i, j, hij);
            let pj_lt_px = pred_lt_pred_of_lt(d, &p, j, x, pos_j, h2); // Lt pj px
            let motive = d.eq_motive(px, &|d, z| d.lt(pj, z));
            let result = d.transport(px, motive, pj_lt_px, cix, eq_px_cix); // Lt pj cix
            let body = d.const_app(logic.or_inr, &[lt_cix_pj, lt_pj_cix, result]);
            d.lam_fv(h2_fv, lt_jx, body)
        };
        let body = d.const_app(
            logic.or_elim,
            &[lt_xj, lt_jx, target, off_j, sub_lt_j, sub_gt_j],
        );
        d.lam_fv(h_fv, lt_ix, body)
    };

    d.const_app(
        logic.or_elim,
        &[lt_xi, lt_ix, target, off_i, on_lt_i, on_gt_i],
    )
}

/// `hij : Lt i j ⊢ Eq Nat (compact_pair i j (expand_pair i j k)) k` —
/// `compact_pair` is a left inverse of `expand_pair` on any `k` (no domain
/// bound needed: neither function references `n`).
fn expand_compact_pair_id(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    hij: ExprId,
) -> ExprId {
    let p = *p;
    let ek = expand_pair(d, i, j, k);
    let cp_ek0 = compact_pair(d, i, j, ek);
    let goal = d.eq(cp_ek0, k);

    expand_pair_cases(
        d,
        &p,
        i,
        j,
        k,
        goal,
        &|d, h| {
            let eq_ek_k = expand_eq_lt(d, &p, i, j, k, h);
            let k_le_i = le_of_lt(d, &p, k, i, h);
            let eq_cik_k = compact_eq_of_le(d, &p, i, k, k_le_i); // Eq (compact i k) k
            let pj = d.pred(j);
            let i_le_pj = i_le_pred_of_lt(d, &p, i, j, hij);
            let k_le_pj = d.lemma(p.le_trans, &[k, i, pj, k_le_i, i_le_pj]);
            let eq_outer = compact_eq_of_le(d, &p, pj, k, k_le_pj); // Eq (compact pj k) k
            let cik = compact(d, i, k);
            let step1 = d.congr(cik, k, eq_cik_k, &|d, z| compact(d, pj, z));
            let cp_k = compact(d, pj, cik); // = compact_pair i j k
            let compact_pj_k = compact(d, pj, k);
            let step2 = d.trans(cp_k, compact_pj_k, k, step1, eq_outer);
            let cp_ek_eq_cp_k = d.congr(ek, k, eq_ek_k, &|d, z| compact_pair(d, i, j, z));
            let cp_ek = compact_pair(d, i, j, ek);
            d.trans(cp_ek, cp_k, k, cp_ek_eq_cp_k, step2)
        },
        &|d, h1, h2| {
            let succ_k = d.succ(k);
            let eq_ek_sk = expand_eq_mid(d, &p, i, j, k, h1, h2);
            let lt_i_succk = d.lemma(p.lt_succ_of_le, &[i, k, h1]);
            let eq_ci_sk_k = compact_eq_of_gt(d, &p, i, succ_k, lt_i_succk); // Eq (compact i succ_k) k
            let pj = d.pred(j);
            let ci_sk = compact(d, i, succ_k);
            let step1 = d.congr(ci_sk, k, eq_ci_sk_k, &|d, z| compact(d, pj, z));
            let succ2_k = d.succ(succ_k);
            let le_succk_pj = d.lemma(p.pred_le_pred, &[succ2_k, j, h2]); // Le succ_k pj
            let le_k_pj = le_of_lt(d, &p, k, pj, le_succk_pj);
            let eq_outer = compact_eq_of_le(d, &p, pj, k, le_k_pj); // Eq (compact pj k) k
            let cp_sk = compact(d, pj, ci_sk); // = compact_pair i j succ_k
            let compact_pj_k = compact(d, pj, k);
            let step2 = d.trans(cp_sk, compact_pj_k, k, step1, eq_outer);
            let cp_ek_eq_cp_sk = d.congr(ek, succ_k, eq_ek_sk, &|d, z| compact_pair(d, i, j, z));
            let cp_ek = compact_pair(d, i, j, ek);
            d.trans(cp_ek, cp_sk, k, cp_ek_eq_cp_sk, step2)
        },
        &|d, h1, h2| {
            let succ_k = d.succ(k);
            let succ2_k = d.succ(succ_k);
            let eq_ek_s2k = expand_eq_hi(d, &p, i, j, k, h1, h2);
            let le_i_succk = d.lemma(p.le_succ_of_le, &[i, k, h1]);
            let lt_i_succ2k = d.lemma(p.lt_succ_of_le, &[i, succ_k, le_i_succk]);
            let eq_ci_s2k_sk = compact_eq_of_gt(d, &p, i, succ2_k, lt_i_succ2k); // Eq (compact i succ2_k) succ_k
            let pj = d.pred(j);
            let ci_s2k = compact(d, i, succ2_k);
            let step1 = d.congr(ci_s2k, succ_k, eq_ci_s2k_sk, &|d, z| compact(d, pj, z));
            let le_j_succk = d.lemma(p.le_of_succ_le_succ, &[j, succ_k, h2]); // Le j succ_k
            let le_pj_k = d.lemma(p.pred_le_pred, &[j, succ_k, le_j_succk]); // Le pj k
            let lt_pj_succk = d.lemma(p.lt_succ_of_le, &[pj, k, le_pj_k]); // Lt pj succ_k
            let eq_outer = compact_eq_of_gt(d, &p, pj, succ_k, lt_pj_succk); // Eq (compact pj succ_k) k
            let cp_s2k = compact(d, pj, ci_s2k); // = compact_pair i j succ2_k
            let compact_pj_sk = compact(d, pj, succ_k);
            let step2 = d.trans(cp_s2k, compact_pj_sk, k, step1, eq_outer);
            let cp_ek_eq_cp_s2k = d.congr(ek, succ2_k, eq_ek_s2k, &|d, z| compact_pair(d, i, j, z));
            let cp_ek = compact_pair(d, i, j, ek);
            d.trans(cp_ek, cp_s2k, k, cp_ek_eq_cp_s2k, step2)
        },
    )
}

/// `x = sigma applied to ek`, `sigma_c = sigma applied to c`. From
/// `hfix_c : Eq (sigma c) c`, `h_ne : Not (Eq ek c)`, and the two bounds
/// `inj`'s `InjectiveOn` hypothesis needs, derive `Not (Eq x c)` — if `x`
/// were `c`, then (using `sigma c = c`) `x = sigma c`, so injectivity would
/// force `ek = c`, contradicting `h_ne`.
#[allow(clippy::too_many_arguments)]
fn ne_of_sigma_apply(
    d: &mut NatDev<'_>,
    x: ExprId,
    ek: ExprId,
    c: ExprId,
    sigma_c: ExprId,
    inj: ExprId,
    ek_lt: ExprId,
    c_lt: ExprId,
    hfix_c: ExprId,
    h_ne: ExprId,
) -> ExprId {
    let eq_x_c = d.eq(x, c);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv); // heq : Eq x c
    let c_eq_sigma_c = d.symm(sigma_c, c, hfix_c); // Eq c sigma_c
    let x_eq_sigma_c = d.trans(x, c, sigma_c, heq, c_eq_sigma_c); // Eq x sigma_c
    let ek_eq_c = d.apply(inj, &[ek, c, ek_lt, c_lt, x_eq_sigma_c]); // Eq ek c
    let false_pf = d.apply(h_ne, &[ek_eq_c]);
    d.lam_fv(heq_fv, eq_x_c, false_pf)
}

// ---------------------------------------------------------------------------
// The two headline theorems.
// ---------------------------------------------------------------------------

/// Declare `Nat.restrict_pair_injective`:
///
/// `∀ σ i j n, InjectiveOn σ (succ (succ n)) → Lt i j →
///   Lt j (succ (succ n)) → setwise_fixed σ i j →
///   InjectiveOn (fun k => compact_pair i j (σ (expand_pair i j k))) n`.
///
/// No `MapsInto` hypothesis is needed (mirroring `restrict_injective`'s own
/// omission of it): every bound the two `compact_injective` applications
/// need comes from `expand_pair_lt_bound` and the hypotheses already in
/// scope, never from `σ`'s codomain.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_restrict_pair_injective(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sn = d.succ(n);
    let ssn = d.succ(sn);

    let inj_ty = d.const_app(p.injective_on, &[sigma, ssn]);
    let inj_fv = d.fresh_fvar();
    let inj = d.kernel().fvar(inj_fv);

    let hij_ty = d.lt(i, j);
    let hij_fv = d.fresh_fvar();
    let hij = d.kernel().fvar(hij_fv);

    let hjn_ty = d.lt(j, ssn);
    let hjn_fv = d.fresh_fvar();
    let hjn = d.kernel().fvar(hjn_fv);

    let sigma_i = d.apply(sigma, &[i]);
    let sigma_j = d.apply(sigma, &[j]);
    let fix_i_ty = d.eq(sigma_i, i);
    let fix_j_ty = d.eq(sigma_j, j);
    let hfix_ty = d.const_app(p.setwise_fixed, &[sigma, i, j]);
    let hfix_fv = d.fresh_fvar();
    let hfix = d.kernel().fvar(hfix_fv);

    let rho = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ek = expand_pair(d, i, j, k);
        let sk = d.apply(sigma, &[ek]);
        let body = compact_pair(d, i, j, sk);
        d.lam_fv(k_fv, nat, body)
    };
    let concl_ty = d.const_app(p.injective_on, &[rho, n]);

    let hfix_i = and_left(d, fix_i_ty, fix_j_ty, hfix);
    let hfix_j = and_right(d, fix_i_ty, fix_j_ty, hfix);

    let j_le_ssn = le_of_lt(d, &p, j, ssn, hjn);
    let i_lt_ssn = d.lemma(p.lt_of_lt_of_le, &[i, j, ssn, hij, j_le_ssn]);

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

    let ek_a = expand_pair(d, i, j, a);
    let ek_b = expand_pair(d, i, j, b);
    let sea = d.apply(sigma, &[ek_a]);
    let seb = d.apply(sigma, &[ek_b]);
    let rho_a = compact_pair(d, i, j, sea);
    let rho_b = compact_pair(d, i, j, seb);
    let heq_ty = d.eq(rho_a, rho_b);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let ek_a_ne_i = expand_pair_ne_i(d, &p, i, j, a);
    let ek_a_ne_j = expand_pair_ne_j(d, &p, i, j, a, hij);
    let ek_b_ne_i = expand_pair_ne_i(d, &p, i, j, b);
    let ek_b_ne_j = expand_pair_ne_j(d, &p, i, j, b, hij);

    let ek_a_lt = expand_pair_lt_bound(d, &p, i, j, n, a, hjn, han);
    let ek_b_lt = expand_pair_lt_bound(d, &p, i, j, n, b, hjn, hbn);

    let xa_ne_i = ne_of_sigma_apply(
        d, sea, ek_a, i, sigma_i, inj, ek_a_lt, i_lt_ssn, hfix_i, ek_a_ne_i,
    );
    let xa_ne_j = ne_of_sigma_apply(
        d, sea, ek_a, j, sigma_j, inj, ek_a_lt, hjn, hfix_j, ek_a_ne_j,
    );
    let xb_ne_i = ne_of_sigma_apply(
        d, seb, ek_b, i, sigma_i, inj, ek_b_lt, i_lt_ssn, hfix_i, ek_b_ne_i,
    );
    let xb_ne_j = ne_of_sigma_apply(
        d, seb, ek_b, j, sigma_j, inj, ek_b_lt, hjn, hfix_j, ek_b_ne_j,
    );

    let off1a = compact_pair_off(d, &p, i, j, sea, hij, xa_ne_i, xa_ne_j);
    let off1b = compact_pair_off(d, &p, i, j, seb, hij, xb_ne_i, xb_ne_j);

    let pj = d.pred(j);
    let cia = compact(d, i, sea);
    let cib = compact(d, i, seb);
    let step1 = compact_injective(d, &p, pj, cia, cib, off1a, off1b, heq); // Eq cia cib

    let off2a = off_from_ne(d, &p, i, sea, xa_ne_i);
    let off2b = off_from_ne(d, &p, i, seb, xb_ne_i);
    let step2 = compact_injective(d, &p, i, sea, seb, off2a, off2b, step1); // Eq sea seb

    let ek_eq = d.apply(inj, &[ek_a, ek_b, ek_a_lt, ek_b_lt, step2]); // Eq ek_a ek_b

    let id_a = expand_compact_pair_id(d, &p, i, j, a, hij); // Eq (compact_pair i j ek_a) a
    let id_b = expand_compact_pair_id(d, &p, i, j, b, hij); // Eq (compact_pair i j ek_b) b
    let cp_congr = d.congr(ek_a, ek_b, ek_eq, &|d, z| compact_pair(d, i, j, z));
    let cp_ek_a = compact_pair(d, i, j, ek_a);
    let cp_ek_b = compact_pair(d, i, j, ek_b);
    let a_eq_cp_ek_a = d.symm(cp_ek_a, a, id_a); // Eq a (compact_pair i j ek_a)
    let step3 = d.trans(a, cp_ek_a, cp_ek_b, a_eq_cp_ek_a, cp_congr);
    let result = d.trans(a, cp_ek_b, b, step3, id_b);

    let inner = d.lam_fv(heq_fv, heq_ty, result);
    let with_hbn = d.lam_fv(hbn_fv, hbn_ty, inner);
    let with_han = d.lam_fv(han_fv, han_ty, with_hbn);
    let with_b = d.lam_fv(b_fv, nat, with_han);
    let with_a = d.lam_fv(a_fv, nat, with_b);

    let val_after_n = {
        let w1 = d.lam_fv(hfix_fv, hfix_ty, with_a);
        let w2 = d.lam_fv(hjn_fv, hjn_ty, w1);
        let w3 = d.lam_fv(hij_fv, hij_ty, w2);
        d.lam_fv(inj_fv, inj_ty, w3)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, val_after_n);
        let with_j = d.lam_fv(j_fv, nat, with_n);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        d.lam_fv(sigma_fv, fn_ty, with_i)
    };

    let stmt_after_n = {
        let w1 = d.arrow(hfix_ty, concl_ty);
        let w2 = d.arrow(hjn_ty, w1);
        let w3 = d.arrow(hij_ty, w2);
        d.arrow(inj_ty, w3)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt_after_n);
        let with_j = d.pi_fv(j_fv, nat, with_n);
        let with_i = d.pi_fv(i_fv, nat, with_j);
        d.pi_fv(sigma_fv, fn_ty, with_i)
    };

    d.declare_theorem(p.restrict_pair_injective, ty, value)
}

/// Declare `Nat.restrict_pair_maps_into`:
///
/// `∀ σ i j n, InjectiveOn σ (succ (succ n)) → MapsInto σ (succ (succ n)) →
///   Lt i j → Lt j (succ (succ n)) → setwise_fixed σ i j →
///   MapsInto (fun k => compact_pair i j (σ (expand_pair i j k))) n`.
///
/// Reuses `finite.rs`'s `compact_lt_of` TWICE, the same composition trick
/// `compact_pair`'s own value lemmas use.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_restrict_pair_maps_into(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sn = d.succ(n);
    let ssn = d.succ(sn);

    let inj_ty = d.const_app(p.injective_on, &[sigma, ssn]);
    let inj_fv = d.fresh_fvar();
    let inj = d.kernel().fvar(inj_fv);

    let maps_ty = d.const_app(p.maps_into, &[sigma, ssn]);
    let maps_fv = d.fresh_fvar();
    let maps = d.kernel().fvar(maps_fv);

    let hij_ty = d.lt(i, j);
    let hij_fv = d.fresh_fvar();
    let hij = d.kernel().fvar(hij_fv);

    let hjn_ty = d.lt(j, ssn);
    let hjn_fv = d.fresh_fvar();
    let hjn = d.kernel().fvar(hjn_fv);

    let sigma_i = d.apply(sigma, &[i]);
    let sigma_j = d.apply(sigma, &[j]);
    let fix_i_ty = d.eq(sigma_i, i);
    let fix_j_ty = d.eq(sigma_j, j);
    let hfix_ty = d.const_app(p.setwise_fixed, &[sigma, i, j]);
    let hfix_fv = d.fresh_fvar();
    let hfix = d.kernel().fvar(hfix_fv);

    let rho = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ek = expand_pair(d, i, j, k);
        let sk = d.apply(sigma, &[ek]);
        let body = compact_pair(d, i, j, sk);
        d.lam_fv(k_fv, nat, body)
    };
    let concl_ty = d.const_app(p.maps_into, &[rho, n]);

    let hfix_i = and_left(d, fix_i_ty, fix_j_ty, hfix);
    let hfix_j = and_right(d, fix_i_ty, fix_j_ty, hfix);

    let j_le_sn = d.lemma(p.le_of_succ_le_succ, &[j, sn, hjn]); // Le j sn
    let i_lt_sn = d.lemma(p.lt_of_lt_of_le, &[i, j, sn, hij, j_le_sn]);
    let i_le_sn = le_of_lt(d, &p, i, sn, i_lt_sn);
    let j_le_ssn = le_of_lt(d, &p, j, ssn, hjn);
    let i_lt_ssn = d.lemma(p.lt_of_lt_of_le, &[i, j, ssn, hij, j_le_ssn]);
    let pj = d.pred(j);
    let pj_le_n = d.lemma(p.pred_le_pred, &[j, sn, j_le_sn]); // Le pj n

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let ek = expand_pair(d, i, j, k);
    let ek_ne_i = expand_pair_ne_i(d, &p, i, j, k);
    let ek_ne_j = expand_pair_ne_j(d, &p, i, j, k, hij);
    let ek_lt = expand_pair_lt_bound(d, &p, i, j, n, k, hjn, hk);

    let x = d.apply(sigma, &[ek]);
    let x_lt = d.apply(maps, &[ek, ek_lt]); // Lt x ssn

    let x_ne_i = ne_of_sigma_apply(d, x, ek, i, sigma_i, inj, ek_lt, i_lt_ssn, hfix_i, ek_ne_i);
    let x_ne_j = ne_of_sigma_apply(d, x, ek, j, sigma_j, inj, ek_lt, hjn, hfix_j, ek_ne_j);

    let off_i_x = off_from_ne(d, &p, i, x, x_ne_i);
    let off_pair_x = compact_pair_off(d, &p, i, j, x, hij, x_ne_i, x_ne_j);

    let x_le_sn = d.lemma(p.le_of_lt_succ, &[x, sn, x_lt]); // Le x sn
    let cix = compact(d, i, x);
    let stage1 = compact_lt_of(d, &p, i, x, sn, i_le_sn, x_le_sn, off_i_x); // Lt cix sn
    let cix_le_n = d.lemma(p.le_of_lt_succ, &[cix, n, stage1]); // Le cix n

    let result = compact_lt_of(d, &p, pj, cix, n, pj_le_n, cix_le_n, off_pair_x); // Lt (compact pj cix) n

    let with_hk = d.lam_fv(hk_fv, hk_ty, result);
    let maps_body = d.lam_fv(k_fv, nat, with_hk);

    let val_after_n = {
        let w1 = d.lam_fv(hfix_fv, hfix_ty, maps_body);
        let w2 = d.lam_fv(hjn_fv, hjn_ty, w1);
        let w3 = d.lam_fv(hij_fv, hij_ty, w2);
        let w4 = d.lam_fv(maps_fv, maps_ty, w3);
        d.lam_fv(inj_fv, inj_ty, w4)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, val_after_n);
        let with_j = d.lam_fv(j_fv, nat, with_n);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        d.lam_fv(sigma_fv, fn_ty, with_i)
    };

    let stmt_after_n = {
        let w1 = d.arrow(hfix_ty, concl_ty);
        let w2 = d.arrow(hjn_ty, w1);
        let w3 = d.arrow(hij_ty, w2);
        let w4 = d.arrow(maps_ty, w3);
        d.arrow(inj_ty, w4)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt_after_n);
        let with_j = d.pi_fv(j_fv, nat, with_n);
        let with_i = d.pi_fv(i_fv, nat, with_j);
        d.pi_fv(sigma_fv, fn_ty, with_i)
    };

    d.declare_theorem(p.restrict_pair_maps_into, ty, value)
}
