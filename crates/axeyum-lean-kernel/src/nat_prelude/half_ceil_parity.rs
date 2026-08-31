//! The parity of `m − ⌊m/2⌋` (i.e. `⌈m/2⌉`), classified by `m mod 4`.
//!
//! This is the arithmetic core of the **second supplementary law of quadratic
//! reciprocity**. Gauss's lemma (`Int.gaussLemmaSignCount`) at `a := 2`,
//! `pp := 2m+1` gives `2^m ≡ (−1)^N [pp]` with `N := gaussNegCount pp 2 m`, and
//! [`NatPrelude::gauss_neg_count_two_closed_form`] evaluates that count to
//! `sub m (div m 2)`. So the whole law reduces to: **is `m − ⌊m/2⌋` even or
//! odd?**
//!
//! ```text
//! m mod 4 | p = 2m+1 mod 8 | N = m − ⌊m/2⌋ | N parity
//!    0    |       1        |     even      |  even
//!    1    |       3        |      odd      |   odd
//!    2    |       5        |      odd      |   odd
//!    3    |       7        |     even      |  even
//! ```
//!
//! Re-runnable check of that table:
//!
//! ```sh
//! python3 -c "
//! import collections
//! agg=collections.defaultdict(set)
//! for m in range(0,200):
//!     p=2*m+1; N=m-(m//2)
//!     agg[m%4].add((p%8, N%2))
//! for k in sorted(agg): print(k, sorted(agg[k]))
//! "
//! # 0 [(1, 0)]   1 [(3, 1)]   2 [(5, 1)]   3 [(7, 0)]
//! ```
//!
//! ## Why a DOUBLE even/odd split, and not `mod 4` arithmetic
//!
//! `Nat.div`/`Nat.mod` are stuck at a symbolic argument, so no `m mod 4`
//! hypothesis can be *evaluated*; a proof that takes one would first have to
//! reconstruct `m`'s shape from it. [`NatPrelude::even_or_odd`] runs the other
//! way round — it *produces* `m = h + h` or `m = succ (h + h)` with the half
//! `h := div m 2` **computed** (never an existential witness; `Exists.rec` is
//! `Prop`-only and cannot produce a term whose type mentions the witness).
//! Applying it twice, at `m` and then at `h` with `q := div h 2`, hands over
//! all four classes with no division ever needing to reduce:
//!
//! ```text
//! m = h+h,        h = q+q        ⟹ m = (q+q)+(q+q)                 N = h      = q+q
//! m = succ (h+h), h = q+q        ⟹ m = succ ((q+q)+(q+q))          N = succ h = succ (q+q)
//! m = h+h,        h = succ (q+q) ⟹ m = succ(q+q) + succ(q+q)       N = h      = succ (q+q)
//! m = succ (h+h), h = succ (q+q) ⟹ m = succ (succ(q+q)+succ(q+q))  N = succ h = succ (succ (q+q))
//! ```
//!
//! (in that order: `m ≡ 0, 1, 2, 3 (mod 4)`.)
//!
//! Both `N` evaluations are one application of
//! [`NatPrelude::add_sub_cancel_left`] (`sub (add x y) x = y`):
//!
//! - even `m`: `sub (add h h) h = h`, at `(x, y) := (h, h)`;
//! - odd `m`: at `(x, y) := (h, succ h)` its statement is
//!   `sub (add h (succ h)) h = succ h`, and `add h (succ h)` is
//!   **definitionally** `succ (add h h)` — `Nat.add` recurses on its right
//!   argument, so the literal `succ` there reduces with no `succ_add` rewrite.
//!   That is the whole reason the symbolic side is kept on the left throughout
//!   this file.
//!
//! The `m ≡ 3` case is the only one needing a real lemma: `succ (succ (q+q))`
//! is `add (succ q) (succ q)` only up to [`super::parity::succ_double_eq`],
//! because `add (succ q) (succ q)` reduces to `succ (add (succ q) q)` and
//! `add (succ q) q` is stuck.
//!
//! [`NatPrelude::gauss_neg_count_two_closed_form`]: super::NatPrelude::gauss_neg_count_two_closed_form
//! [`NatPrelude::even_or_odd`]: super::NatPrelude::even_or_odd
//! [`NatPrelude::add_sub_cancel_left`]: super::NatPrelude::add_sub_cancel_left

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use super::parity::{even_predicate, odd_predicate, succ_double_eq};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// The four residue shapes of `m` modulo 4, in terms of `q := div (div m 2) 2`.
///
/// Index `r` is the shape of an `m` with `m ≡ r (mod 4)`; at `pp := 2m+1` those
/// are `pp = 8q+1`, `8q+3`, `8q+5`, `8q+7` respectively — i.e. index `0` and
/// `3` are exactly `p ≡ ±1 (mod 8)`.
fn class_shape(d: &mut NatDev<'_>, q: ExprId, r: u8) -> ExprId {
    let qq = d.add(q, q);
    let sqq = d.succ(qq);
    match r {
        0 => d.add(qq, qq),
        1 => {
            let inner = d.add(qq, qq);
            d.succ(inner)
        }
        2 => d.add(sqq, sqq),
        _ => {
            let inner = d.add(sqq, sqq);
            d.succ(inner)
        }
    }
}

/// `Or (Eq m (class_shape q a)) (Eq m (class_shape q b))`.
fn class_disjunction(d: &mut NatDev<'_>, m: ExprId, q: ExprId, a: u8, b: u8) -> ExprId {
    let logic = d.prelude().logic;
    let sa = class_shape(d, q, a);
    let sb = class_shape(d, q, b);
    let left = d.eq(m, sa);
    let right = d.eq(m, sb);
    d.const_app(logic.or, &[left, right])
}

/// The four component types of the statement, for a given `m`:
/// `(p ≡ ±1 (mod 8) classes, p ≡ ±3 (mod 8) classes, Even N, Odd N)`.
fn components(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> [ExprId; 4] {
    let p = *p;
    let two = d.num(2);
    let half = d.div(m, two);
    let quarter = d.div(half, two);
    let count = d.sub(m, half);

    let plus_classes = class_disjunction(d, m, quarter, 0, 3);
    let minus_classes = class_disjunction(d, m, quarter, 1, 2);
    let even_count = d.const_app(p.even, &[count]);
    let odd_count = d.const_app(p.odd, &[count]);
    [plus_classes, minus_classes, even_count, odd_count]
}

/// `Nat.half_ceil_parity` — see the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_half_ceil_parity(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let logic = p.logic;

    d.theorem(p.half_ceil_parity, 1, &|d, values| {
        let m = values[0];
        let nat = d.nat_ty();
        let anon = d.anon_name();
        let uone = d.level_one();

        let two = d.num(2);
        let half = d.div(m, two);
        let quarter = d.div(half, two);
        let count = d.sub(m, half);

        let [plus_classes, minus_classes, even_count, odd_count] = components(d, &p, m);
        let left_conj = d.const_app(logic.and, &[plus_classes, even_count]);
        let right_conj = d.const_app(logic.and, &[minus_classes, odd_count]);
        let target = d.const_app(logic.or, &[left_conj, right_conj]);

        // `hm : m = <shape in half>` ⊢ `sub m half = half` (even `m`) or
        // `sub m half = succ half` (odd `m`). `congr` moves `hm` under
        // `fun x => sub x half`, then `add_sub_cancel_left` evaluates.
        let count_value = |d: &mut NatDev<'_>, hm: ExprId, m_is_even: bool| -> ExprId {
            let hh = d.add(half, half);
            let succ_half = d.succ(half);
            let (m_shape, cancel_arg) = if m_is_even {
                (hh, half)
            } else {
                let succ_hh = d.succ(hh);
                (succ_hh, succ_half)
            };
            let step_shape = d.congr(m, m_shape, hm, &|d, x| d.sub(x, half));
            let sub_shape = d.sub(m_shape, half);
            // For odd `m` the lemma's own LHS is `sub (add half (succ half))
            // half`, which is DEFINITIONALLY `sub_shape` (see the module doc).
            let step_cancel = d.lemma(p.add_sub_cancel_left, &[half, cancel_arg]);
            let (_, proof) = d.chain(count, &[(sub_shape, step_shape), (cancel_arg, step_cancel)]);
            proof
        };

        // One of the four leaves. `hm : m = <shape in half>`,
        // `hh : half = <shape in quarter>`.
        let leaf = |d: &mut NatDev<'_>,
                    hm: ExprId,
                    hh: ExprId,
                    m_is_even: bool,
                    half_is_even: bool|
         -> ExprId {
            let qq = d.add(quarter, quarter);
            let sqq = d.succ(qq);
            let half_shape = if half_is_even { qq } else { sqq };

            // --- the class equation `m = class_shape quarter r` -------------
            let double_or_succ = move |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let doubled = d.add(x, x);
                if m_is_even { doubled } else { d.succ(doubled) }
            };
            let from_half = double_or_succ(d, half);
            let from_quarter = double_or_succ(d, half_shape);
            let step_shape = d.congr(half, half_shape, hh, &double_or_succ);
            let (_, class_eq) = d.chain(m, &[(from_half, hm), (from_quarter, step_shape)]);

            // --- the count equation `sub m half = <the parity witness>` -----
            let hcount = count_value(d, hm, m_is_even);
            let succ_if_odd_m = move |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                if m_is_even { x } else { d.succ(x) }
            };
            let count_at_half = succ_if_odd_m(d, half);
            let count_at_quarter = succ_if_odd_m(d, half_shape);
            let step_half = d.congr(half, half_shape, hh, &succ_if_odd_m);
            let (_, count_eq) = d.chain(
                count,
                &[(count_at_half, hcount), (count_at_quarter, step_half)],
            );

            // `count_at_quarter` is `q+q`, `succ (q+q)`, `succ (q+q)` or
            // `succ (succ (q+q))` in the four cases. The first three already
            // have `Even`/`Odd`'s own witness shape at `q`; the last needs
            // `succ_double_eq` to become `add (succ q) (succ q)`.
            let parity_is_even = m_is_even == half_is_even;
            let (witness, count_final) = if parity_is_even && !m_is_even {
                // m odd, half odd: `count = succ (succ (q+q))`.
                let succ_q = d.succ(quarter);
                let doubled = d.add(succ_q, succ_q);
                // `add (succ q) (succ q) = succ (succ (q+q))`; flip it.
                let dbl = succ_double_eq(d, &p, quarter);
                let flipped = d.symm(doubled, count_at_quarter, dbl);
                let (_, proof) =
                    d.chain(count, &[(count_at_quarter, count_eq), (doubled, flipped)]);
                (succ_q, proof)
            } else {
                (quarter, count_eq)
            };

            let parity_proof = {
                let pred = if parity_is_even {
                    even_predicate(d, count)
                } else {
                    odd_predicate(d, count)
                };
                let intro = d.kernel().const_(logic.exists_intro, vec![uone]);
                d.apply(intro, &[nat, pred, witness, count_final])
            };

            // In BOTH pairs the left disjunct is the one with the even half
            // (`m ≡ 0` in the `plus` pair, `m ≡ 1` in the `minus` pair).
            let other_index: u8 = match (parity_is_even, m_is_even) {
                (true, true) => 3,
                (true, false) => 0,
                (false, true) => 1,
                (false, false) => 2,
            };
            let this_eq = d.eq(m, from_quarter);
            let other_shape = class_shape(d, quarter, other_index);
            let other_eq = d.eq(m, other_shape);
            let class_proof = if half_is_even {
                d.const_app(logic.or_inl, &[this_eq, other_eq, class_eq])
            } else {
                d.const_app(logic.or_inr, &[other_eq, this_eq, class_eq])
            };

            let conj = if parity_is_even {
                d.const_app(
                    logic.and_intro,
                    &[plus_classes, even_count, class_proof, parity_proof],
                )
            } else {
                d.const_app(
                    logic.and_intro,
                    &[minus_classes, odd_count, class_proof, parity_proof],
                )
            };
            if parity_is_even {
                d.const_app(logic.or_inl, &[left_conj, right_conj, conj])
            } else {
                d.const_app(logic.or_inr, &[left_conj, right_conj, conj])
            }
        };

        // Inner split: `even_or_odd half`, under a fixed outer branch.
        let inner = |d: &mut NatDev<'_>, hm: ExprId, m_is_even: bool| -> ExprId {
            let qq = d.add(quarter, quarter);
            let sqq = d.succ(qq);
            let half_even_disj = d.eq(half, qq);
            let half_odd_disj = d.eq(half, sqq);

            let minor_even = {
                let fv = d.fresh_fvar();
                let hh = d.kernel().fvar(fv);
                let body = leaf(d, hm, hh, m_is_even, true);
                d.lam_fv(fv, half_even_disj, body)
            };
            let minor_odd = {
                let fv = d.fresh_fvar();
                let hh = d.kernel().fvar(fv);
                let body = leaf(d, hm, hh, m_is_even, false);
                d.lam_fv(fv, half_odd_disj, body)
            };
            let motive = {
                let or_ty = d.const_app(logic.or, &[half_even_disj, half_odd_disj]);
                d.kernel().lam(anon, or_ty, target, BinderInfo::Default)
            };
            let hsplit = d.lemma(p.even_or_odd, &[half]);
            let or_rec = d.kernel().const_(logic.or_rec, vec![]);
            d.apply(
                or_rec,
                &[
                    half_even_disj,
                    half_odd_disj,
                    motive,
                    minor_even,
                    minor_odd,
                    hsplit,
                ],
            )
        };

        // Outer split: `even_or_odd m`.
        let hh_m = d.add(half, half);
        let shh_m = d.succ(hh_m);
        let m_even_disj = d.eq(m, hh_m);
        let m_odd_disj = d.eq(m, shh_m);

        let minor_even = {
            let fv = d.fresh_fvar();
            let hm = d.kernel().fvar(fv);
            let body = inner(d, hm, true);
            d.lam_fv(fv, m_even_disj, body)
        };
        let minor_odd = {
            let fv = d.fresh_fvar();
            let hm = d.kernel().fvar(fv);
            let body = inner(d, hm, false);
            d.lam_fv(fv, m_odd_disj, body)
        };
        let motive = {
            let or_ty = d.const_app(logic.or, &[m_even_disj, m_odd_disj]);
            d.kernel().lam(anon, or_ty, target, BinderInfo::Default)
        };
        let hsplit = d.lemma(p.even_or_odd, &[m]);
        let or_rec = d.kernel().const_(logic.or_rec, vec![]);
        let proof = d.apply(
            or_rec,
            &[
                m_even_disj,
                m_odd_disj,
                motive,
                minor_even,
                minor_odd,
                hsplit,
            ],
        );
        (target, proof)
    })?;
    Ok(())
}

/// Declare everything in this module.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_half_ceil_parity_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_half_ceil_parity(d, p)
}
