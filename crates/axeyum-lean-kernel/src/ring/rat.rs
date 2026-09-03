//! The ℚ fragment: parse `ExprId`s into a canonical **signed** sum of
//! monomials, and emit a kernel proof term for `t₁ = t₂` when the two sides
//! agree — [`super::int`]'s shape again, over `Rat` instead of `Int`
//! (ADR-1582). Division stays [`Decline::NonRing`]: `Rat.div a b := mul a
//! (inv b)`, and `inv` is not a ring operation.
//!
//! ## What differs from [`super::int`]
//!
//! - **`Rat` already has the two internally-derived primitives `super::int`
//!   had to build by hand.** `Rat.neg_neg` and `Rat.neg_mul` are both public
//!   `RatPrelude` theorems (proved from `neg_eq_of_add_eq_zero`'s uniqueness
//!   argument, cheaper over a field than `super::int::neg_neg_lemma`'s
//!   `neg_one_mul` chain), so `flatten_neg`'s double-negation case and
//!   [`super::int`]'s `apply_mono_signs` sign-wrapping use them directly —
//!   no internal derivation needed.
//! - **No free numeral-splitting reduction, so coefficients are capped at
//!   magnitude 1.** `super::int::scale_unsigned` builds `mul it (ofNat i) =
//!   mul it (ofNat (i-1)) + it` by splitting `ofNat i = ofNat (i-1) + ofNat
//!   1`, a **closed** `Int` reduction (both sides concrete `ofNat`
//!   applications). `Rat`'s own numerals have no such shortcut — a rational
//!   literal is a normalized `num/den` pair (`Rat.mk`/`Rat.normalize`), and
//!   `Rat.add` between two of them cross-multiplies and re-normalizes
//!   through a real GCD computation, not a `succ`/`ofNat`-style structural
//!   recursion that reduces for free on concrete arguments the way `Int.add`
//!   (never mind `Nat.add`) does. Building that bridge would need a genuine
//!   `Rat`-numeral-arithmetic lemma this producer does not have and none of
//!   its five retirement targets need — `scale_item` therefore only handles
//!   `count ∈ {-1, 0, 1}` and declines [`Decline::CoefficientTooLarge`]
//!   otherwise, tighter than [`super::MAX_COEFF`]. `as_numeral` itself only
//!   ever recognizes `{-1, 0, 1}` (`Rat.zero`/`Rat.one`/`neg` of either), so
//!   the decline is **currently unreachable** from any goal this producer's
//!   own recognizer can construct — a `2` is spelled `add one one` and goes
//!   through the ordinary additive route instead (see
//!   `a_numeral_two_spelled_as_one_plus_one_is_still_proved`), not through a
//!   capped coefficient. The check is defensive, kept for the same reason
//!   `combine_items`'s `Num*Num` overflow check is, not because a test
//!   exercises its failing side. A sound, documented, sized restriction, the
//!   same spirit as `super::nat`'s original
//!   no-intra-monomial-sorting gap.
//! - **No [`super::int::Problem::cancel_pairs`].** None of the five ℚ
//!   targets produce an `x + (-x)` summand pair, so it was not built —
//!   `super::int`'s own "don't build a speculative capability with no test
//!   exercising it honestly" rule.
//!
//! ## Lemma table
//!
//! | lemma | role |
//! | --- | --- |
//! | `Rat.add_assoc` / `Rat.add_comm` | the outer sum's normalizer |
//! | `Rat.mul_assoc` | merging two monomials' factor lists |
//! | `Rat.mul_comm` | flipping a numeral coefficient, and factor sorting |
//! | `Rat.left_distrib` / `Rat.right_distrib` | distributing a sum across a product, either side |
//! | `Rat.neg_add` | distributing `neg` over a sum |
//! | `Rat.mul_neg` / `Rat.neg_mul` | distributing `neg` out of either factor of a product |
//! | `Rat.neg_neg` | double negation |
//! | `Rat.mul_zero` / `Rat.mul_one` | the `count ∈ {0, 1}` coefficient base cases |

use crate::ExprNode;
use crate::RatPrelude;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{
    radd, rat_ty, rchain, rcongr, rmul, rneg, rone, rrefl, rsymm, rtrans, rzero,
};

use super::{Coeff, Decline};

/// `min(MAX_COEFF, 1)` — see the module docs on why ℚ's coefficient bound is
/// tighter than ℕ/ℤ's.
const MAX_RAT_COEFF: Coeff = 1;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Item {
    Mono(Vec<usize>, bool),
    Num(Coeff),
}

impl Item {
    fn key(&self) -> (bool, &[usize], bool) {
        match self {
            Item::Mono(v, neg) => (false, v.as_slice(), *neg),
            Item::Num(_) => (true, &[], false),
        }
    }

    fn negated(&self) -> Item {
        match self {
            Item::Mono(v, neg) => Item::Mono(v.clone(), !neg),
            Item::Num(k) => Item::Num(-k),
        }
    }
}

struct Problem {
    prelude: RatPrelude,
    atoms: Vec<ExprId>,
}

impl Problem {
    fn new(prelude: &RatPrelude) -> Self {
        Self {
            prelude: *prelude,
            atoms: Vec::new(),
        }
    }

    fn atom_index(&mut self, e: ExprId) -> usize {
        if let Some(i) = self.atoms.iter().position(|&a| a == e) {
            return i;
        }
        self.atoms.push(e);
        self.atoms.len() - 1
    }

    // --- parsing ----------------------------------------------------------

    fn spine(d: &mut IntDev<'_>, e: ExprId) -> (ExprId, Vec<ExprId>) {
        let mut args = Vec::new();
        let mut head = e;
        loop {
            let node = d.kernel().expr_node(head).clone();
            let ExprNode::App(f, a) = node else { break };
            args.push(a);
            head = f;
        }
        args.reverse();
        (head, args)
    }

    fn head_const(d: &mut IntDev<'_>, e: ExprId) -> Option<crate::NameId> {
        match d.kernel().expr_node(e).clone() {
            ExprNode::Const(n, _) => Some(n),
            _ => None,
        }
    }

    /// `e` as a literal `Rat`: `Rat.zero`, `Rat.one`, or `Rat.neg` of either
    /// — the same shape `linarith::int`/`super::int` recognize, restricted
    /// to what this fragment's `count ∈ {-1,0,1}` coefficient cap needs.
    fn as_numeral(&self, d: &mut IntDev<'_>, e: ExprId) -> Option<Coeff> {
        let p = self.prelude;
        if let Some(name) = Self::head_const(d, e) {
            if name == p.zero {
                return Some(0);
            }
            if name == p.one {
                return Some(1);
            }
        }
        let (head, args) = Self::spine(d, e);
        let name = Self::head_const(d, head)?;
        if name == d.int().rat_neg && args.len() == 1 {
            return self.as_numeral(d, args[0]).map(|k| -k);
        }
        None
    }

    fn parse_eq_goal(
        &mut self,
        d: &mut IntDev<'_>,
        e: ExprId,
    ) -> Result<(ExprId, ExprId), Decline> {
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        let name = Self::head_const(d, head).ok_or(Decline::GoalNotAtomic)?;
        if name == d.int().logic.eq && args.len() == 3 {
            let rat_ty_ = rat_ty(d);
            if args[0] == rat_ty_ {
                return Ok((args[1], args[2]));
            }
        }
        let _ = p;
        Err(Decline::GoalNotAtomic)
    }

    // --- term builders ------------------------------------------------------

    fn build_numeral(&self, d: &mut IntDev<'_>, k: u32) -> ExprId {
        let p = self.prelude;
        if k == 0 { rzero(d, p) } else { rone(d, p) }
    }

    fn build_numeral_signed(&self, d: &mut IntDev<'_>, k: Coeff) -> ExprId {
        if k >= 0 {
            self.build_numeral(d, u32::try_from(k).unwrap_or(0))
        } else {
            let base = self.build_numeral(d, u32::try_from(-k).unwrap_or(0));
            rneg(d, base)
        }
    }

    fn item_term(&self, d: &mut IntDev<'_>, item: &Item) -> ExprId {
        match item {
            Item::Mono(vars, neg) => {
                let base = self.fold_mul(d, vars);
                if *neg { rneg(d, base) } else { base }
            }
            Item::Num(k) => self.build_numeral_signed(d, *k),
        }
    }

    fn fold(&self, d: &mut IntDev<'_>, items: &[Item]) -> ExprId {
        let mut acc = self.item_term(d, &items[0]);
        for item in &items[1..] {
            let t = self.item_term(d, item);
            acc = radd(d, acc, t);
        }
        acc
    }

    fn fold_from(&self, d: &mut IntDev<'_>, start: ExprId, items: &[Item]) -> ExprId {
        let mut acc = start;
        for item in items {
            let t = self.item_term(d, item);
            acc = radd(d, acc, t);
        }
        acc
    }

    fn fold_mul(&self, d: &mut IntDev<'_>, vars: &[usize]) -> ExprId {
        let mut acc = self.atoms[vars[0]];
        for &v in &vars[1..] {
            let t = self.atoms[v];
            acc = rmul(d, acc, t);
        }
        acc
    }

    fn fold_mul_from(&self, d: &mut IntDev<'_>, start: ExprId, vars: &[usize]) -> ExprId {
        let mut acc = start;
        for &v in vars {
            let t = self.atoms[v];
            acc = rmul(d, acc, t);
        }
        acc
    }

    // --- outer-sum re-association / sorting (mirrors `int::Problem`) -------

    fn reassoc(&self, d: &mut IntDev<'_>, left: &[Item], right: &[Item]) -> ExprId {
        let fl = self.fold(d, left);
        if right.len() == 1 {
            let joined = self.fold_from(d, fl, right);
            return rrefl(d, joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, &last[0]);
        let fr = radd(d, fi, last_t);
        let p = self.prelude;

        let source = radd(d, fl, fr);
        let regrouped_inner = radd(d, fl, fi);
        let regrouped = radd(d, regrouped_inner, last_t);
        let assoc = d.const_app(p.add_assoc, &[fl, fi, last_t]);
        let step1 = rsymm(d, regrouped, source, assoc);

        let inner = self.reassoc(d, left, init);
        let mut joined_items = left.to_vec();
        joined_items.extend_from_slice(init);
        let joined_inner = self.fold(d, &joined_items);
        let step2 = rcongr(d, regrouped_inner, joined_inner, inner, &|d, x| {
            radd(d, x, last_t)
        });
        let target = radd(d, joined_inner, last_t);
        rtrans(d, source, regrouped, target, step1, step2)
    }

    fn reassoc_mul(&self, d: &mut IntDev<'_>, left: &[usize], right: &[usize]) -> ExprId {
        let fl = self.fold_mul(d, left);
        if right.len() == 1 {
            let joined = rmul(d, fl, self.atoms[right[0]]);
            return rrefl(d, joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold_mul(d, init);
        let last_t = self.atoms[last[0]];
        let fr = rmul(d, fi, last_t);
        let p = self.prelude;

        let source = rmul(d, fl, fr);
        let regrouped_inner = rmul(d, fl, fi);
        let regrouped = rmul(d, regrouped_inner, last_t);
        let assoc = d.const_app(p.mul_assoc, &[fl, fi, last_t]);
        let step1 = rsymm(d, regrouped, source, assoc);

        let inner = self.reassoc_mul(d, left, init);
        let mut joined_vars = left.to_vec();
        joined_vars.extend_from_slice(init);
        let joined_inner = self.fold_mul(d, &joined_vars);
        let step2 = rcongr(d, regrouped_inner, joined_inner, inner, &|d, x| {
            rmul(d, x, last_t)
        });
        let target = rmul(d, joined_inner, last_t);
        rtrans(d, source, regrouped, target, step1, step2)
    }

    /// Sort a monomial's factor list into canonical (index) order —
    /// `super::int::Problem::sort_factors` ported to `Rat`.
    fn sort_factors(&self, d: &mut IntDev<'_>, vars: &[usize]) -> (Vec<usize>, ExprId) {
        let source = self.fold_mul(d, vars);
        let mut current: Vec<usize> = vars.to_vec();
        let mut proof = rrefl(d, source);
        let mut folded = source;
        loop {
            let mut swapped = false;
            for k in 0..current.len().saturating_sub(1) {
                if current[k] <= current[k + 1] {
                    continue;
                }
                let p = self.prelude;
                let x = self.atoms[current[k]];
                let y = self.atoms[current[k + 1]];
                let (inner_before, inner_after, base) = if k == 0 {
                    let before = rmul(d, x, y);
                    let after = rmul(d, y, x);
                    let lemma = d.const_app(p.mul_comm, &[x, y]);
                    (before, after, lemma)
                } else {
                    let prefix = self.fold_mul(d, &current[..k]);
                    let before_inner = rmul(d, prefix, x);
                    let before = rmul(d, before_inner, y);
                    let xy = rmul(d, x, y);
                    let assoc1 = d.const_app(p.mul_assoc, &[prefix, x, y]);
                    let mid1 = rmul(d, prefix, xy);
                    let comm = d.const_app(p.mul_comm, &[x, y]);
                    let yx = rmul(d, y, x);
                    let step2 = rcongr(d, xy, yx, comm, &|d, t| rmul(d, prefix, t));
                    let mid2 = rmul(d, prefix, yx);
                    let after_inner = rmul(d, prefix, y);
                    let after = rmul(d, after_inner, x);
                    let assoc2 = d.const_app(p.mul_assoc, &[prefix, y, x]);
                    let step3 = rsymm(d, after, mid2, assoc2);
                    let (_, base) =
                        rchain(d, before, &[(mid1, assoc1), (mid2, step2), (after, step3)]);
                    (before, after, base)
                };
                let tail = current[k + 2..].to_vec();
                let step = rcongr(d, inner_before, inner_after, base, &|d, t| {
                    self.fold_mul_from(d, t, &tail)
                });
                current.swap(k, k + 1);
                let next = self.fold_mul(d, &current);
                proof = rtrans(d, source, folded, next, proof, step);
                folded = next;
                swapped = true;
            }
            if !swapped {
                break;
            }
        }
        (current, proof)
    }

    fn sort_items(&self, d: &mut IntDev<'_>, items: &[Item]) -> (Vec<Item>, ExprId) {
        let source = self.fold(d, items);
        let mut current: Vec<Item> = items.to_vec();
        let mut proof = rrefl(d, source);
        let mut folded = source;
        loop {
            let mut swapped = false;
            for k in 0..current.len().saturating_sub(1) {
                if current[k].key() <= current[k + 1].key() {
                    continue;
                }
                let p = self.prelude;
                let x = self.item_term(d, &current[k]);
                let y = self.item_term(d, &current[k + 1]);
                let (inner_before, inner_after, base) = if k == 0 {
                    let before = radd(d, x, y);
                    let after = radd(d, y, x);
                    let lemma = d.const_app(p.add_comm, &[x, y]);
                    (before, after, lemma)
                } else {
                    let prefix = self.fold(d, &current[..k]);
                    let before_inner = radd(d, prefix, x);
                    let before = radd(d, before_inner, y);
                    let xy = radd(d, x, y);
                    let assoc1 = d.const_app(p.add_assoc, &[prefix, x, y]);
                    let mid1 = radd(d, prefix, xy);
                    let comm = d.const_app(p.add_comm, &[x, y]);
                    let yx = radd(d, y, x);
                    let step2 = rcongr(d, xy, yx, comm, &|d, t| radd(d, prefix, t));
                    let mid2 = radd(d, prefix, yx);
                    let after_inner = radd(d, prefix, y);
                    let after = radd(d, after_inner, x);
                    let assoc2 = d.const_app(p.add_assoc, &[prefix, y, x]);
                    let step3 = rsymm(d, after, mid2, assoc2);
                    let (_, base) =
                        rchain(d, before, &[(mid1, assoc1), (mid2, step2), (after, step3)]);
                    (before, after, base)
                };
                let tail = current[k + 2..].to_vec();
                let step = rcongr(d, inner_before, inner_after, base, &|d, t| {
                    self.fold_from(d, t, &tail)
                });
                current.swap(k, k + 1);
                let next = self.fold(d, &current);
                proof = rtrans(d, source, folded, next, proof, step);
                folded = next;
                swapped = true;
            }
            if !swapped {
                break;
            }
        }
        (current, proof)
    }

    // --- the multiplicative "unroll" (magnitude capped at 1) --------------

    /// `Eq Rat (mul it (numeral count)) (fold result)`, or — with
    /// `commuted` — `Eq Rat (mul (numeral count) it) (fold result)`.
    /// `count` restricted to `{-1, 0, 1}` — see the module docs.
    fn scale_item(
        &mut self,
        d: &mut IntDev<'_>,
        item: &Item,
        count: Coeff,
        commuted: bool,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        if count.unsigned_abs() > MAX_RAT_COEFF.unsigned_abs() {
            return Err(Decline::CoefficientTooLarge);
        }
        let p = self.prelude;
        let it = self.item_term(d, item);

        let (items, uncommuted_lhs, base_proof) = if count == 0 {
            let zero = rzero(d, p);
            let proof = d.const_app(p.mul_zero, &[it]);
            (vec![Item::Num(0)], rmul(d, it, zero), proof)
        } else if count == 1 {
            let proof = d.const_app(p.mul_one, &[it]);
            let one = self.build_numeral(d, 1);
            (vec![item.clone()], rmul(d, it, one), proof)
        } else {
            // count == -1: `mul it (neg one) = neg (mul it one) = neg it`.
            let one = self.build_numeral(d, 1);
            let neg_one = rneg(d, one);
            let mul_it_negone = rmul(d, it, neg_one);
            let mn = d.const_app(p.mul_neg, &[it, one]);
            let mul_it_one = rmul(d, it, one);
            let mo = d.const_app(p.mul_one, &[it]);
            let neg_mul_it_one = rneg(d, mul_it_one);
            let target = rneg(d, it);
            let congr_mo = rcongr(d, mul_it_one, it, mo, &|d, t| rneg(d, t));
            let (_, proof) = rchain(
                d,
                mul_it_negone,
                &[(neg_mul_it_one, mn), (target, congr_mo)],
            );
            (vec![item.negated()], mul_it_negone, proof)
        };

        if commuted {
            let numeral = self.build_numeral_signed(d, count);
            let commuted_lhs = rmul(d, numeral, it);
            let comm = d.const_app(p.mul_comm, &[numeral, it]);
            let target = self.fold(d, &items);
            let full = rtrans(d, commuted_lhs, uncommuted_lhs, target, comm, base_proof);
            Ok((items, full))
        } else {
            Ok((items, base_proof))
        }
    }

    /// `Eq Rat (mul (item_term a) (item_term b)) (fold result)`.
    fn combine_items(
        &mut self,
        d: &mut IntDev<'_>,
        a: &Item,
        b: &Item,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        match (a, b) {
            (Item::Num(x), Item::Num(y)) => {
                if x.unsigned_abs() > MAX_RAT_COEFF.unsigned_abs()
                    || y.unsigned_abs() > MAX_RAT_COEFF.unsigned_abs()
                {
                    return Err(Decline::CoefficientTooLarge);
                }
                self.scale_item(d, &Item::Num(*x), *y, false)
            }
            (Item::Num(k), Item::Mono(_, _)) => self.scale_item(d, b, *k, true),
            (Item::Mono(_, _), Item::Num(k)) => self.scale_item(d, a, *k, false),
            (Item::Mono(va, sign_a), Item::Mono(vb, sign_b)) => {
                let raw_a = self.fold_mul(d, va);
                let raw_b = self.fold_mul(d, vb);
                let mut merged = va.clone();
                merged.extend_from_slice(vb);
                let reassoc = self.reassoc_mul(d, va, vb);
                let merged_term = self.fold_mul(d, &merged);
                let (sorted, sort_proof) = self.sort_factors(d, &merged);
                let sorted_term = self.fold_mul(d, &sorted);
                let raw_prod = rmul(d, raw_a, raw_b);
                let raw_proof = rtrans(d, raw_prod, merged_term, sorted_term, reassoc, sort_proof);

                let (result_sign, source, proof) = apply_mono_signs(
                    d,
                    self.prelude,
                    *sign_a,
                    *sign_b,
                    raw_a,
                    raw_b,
                    raw_prod,
                    raw_proof,
                    sorted_term,
                );
                let _ = source;
                Ok((vec![Item::Mono(sorted, result_sign)], proof))
            }
        }
    }

    /// `Eq Rat (mul (item_term item) (fold iv)) (fold result)`.
    fn distribute_single(
        &mut self,
        d: &mut IntDev<'_>,
        item: &Item,
        iv: &[Item],
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        if iv.len() == 1 {
            return self.combine_items(d, item, &iv[0]);
        }
        let (init, last) = iv.split_at(iv.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, &last[0]);
        let fv = radd(d, fi, last_t);
        let it = self.item_term(d, item);
        let source = rmul(d, it, fv);
        let p = self.prelude;

        let mul_it_fi = rmul(d, it, fi);
        let mul_it_last = rmul(d, it, last_t);
        let sum = radd(d, mul_it_fi, mul_it_last);
        let ld = d.const_app(p.left_distrib, &[it, fi, last_t]);

        let (items_init, proof_init) = self.distribute_single(d, item, init)?;
        let (items_last, proof_last) = self.combine_items(d, item, &last[0])?;
        let target_init = self.fold(d, &items_init);
        let target_last = self.fold(d, &items_last);
        let step_a = rcongr(d, mul_it_fi, target_init, proof_init, &|d, t| {
            radd(d, t, mul_it_last)
        });
        let mid2 = radd(d, target_init, mul_it_last);
        let step_b = rcongr(d, mul_it_last, target_last, proof_last, &|d, t| {
            radd(d, target_init, t)
        });
        let mid3 = radd(d, target_init, target_last);
        let step_ab = rtrans(d, sum, mid2, mid3, step_a, step_b);

        let mut items = items_init.clone();
        items.extend_from_slice(&items_last);
        let combined = self.fold(d, &items);
        let reassoc = self.reassoc(d, &items_init, &items_last);
        let joined_proof = rtrans(d, sum, mid3, combined, step_ab, reassoc);
        let full = rtrans(d, source, sum, combined, ld, joined_proof);
        Ok((items, full))
    }

    /// `Eq Rat (mul (fold iu) (fold iv)) (fold result)`, via
    /// `Rat.right_distrib` peeling one summand at a time.
    fn distribute(
        &mut self,
        d: &mut IntDev<'_>,
        iu: &[Item],
        iv: &[Item],
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        if iu.len() == 1 {
            return self.distribute_single(d, &iu[0], iv);
        }
        let (init, last) = iu.split_at(iu.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, &last[0]);
        let fu = radd(d, fi, last_t);
        let fv = self.fold(d, iv);
        let source = rmul(d, fu, fv);
        let p = self.prelude;

        let mul_fi_fv = rmul(d, fi, fv);
        let mul_last_fv = rmul(d, last_t, fv);
        let sum = radd(d, mul_fi_fv, mul_last_fv);
        let rd = d.const_app(p.right_distrib, &[fi, last_t, fv]);

        let (items_init, proof_init) = self.distribute(d, init, iv)?;
        let (items_last, proof_last) = self.distribute_single(d, &last[0], iv)?;
        let target_init = self.fold(d, &items_init);
        let target_last = self.fold(d, &items_last);
        let step_a = rcongr(d, mul_fi_fv, target_init, proof_init, &|d, t| {
            radd(d, t, mul_last_fv)
        });
        let mid2 = radd(d, target_init, mul_last_fv);
        let step_b = rcongr(d, mul_last_fv, target_last, proof_last, &|d, t| {
            radd(d, target_init, t)
        });
        let mid3 = radd(d, target_init, target_last);
        let step_ab = rtrans(d, sum, mid2, mid3, step_a, step_b);

        let mut items = items_init.clone();
        items.extend_from_slice(&items_last);
        let combined = self.fold(d, &items);
        let reassoc = self.reassoc(d, &items_init, &items_last);
        let joined_proof = rtrans(d, sum, mid3, combined, step_ab, reassoc);
        let full = rtrans(d, source, sum, combined, rd, joined_proof);
        Ok((items, full))
    }

    // --- flatten: source term -> raw item list -----------------------------

    fn flatten(&mut self, d: &mut IntDev<'_>, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        if let Some(k) = self.as_numeral(d, e) {
            let items = vec![Item::Num(k)];
            let folded = self.fold(d, &items);
            let proof = rrefl(d, folded);
            return Ok((items, proof));
        }
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head) {
            if name == p.div && !args.is_empty() {
                return Err(Decline::NonRing);
            }
            if name == d.int().rat_add && args.len() == 2 {
                return self.flatten_add(d, args[0], args[1]);
            }
            if name == p.sub && args.len() == 2 {
                let negb = rneg(d, args[1]);
                return self.flatten_add(d, args[0], negb);
            }
            if name == d.int().rat_neg && args.len() == 1 {
                return self.flatten_neg(d, args[0]);
            }
            if name == d.int().rat_mul && args.len() == 2 {
                return self.flatten_mul(d, args[0], args[1]);
            }
        }
        let index = self.atom_index(e);
        let items = vec![Item::Mono(vec![index], false)];
        let proof = rrefl(d, e);
        Ok((items, proof))
    }

    fn flatten_add(
        &mut self,
        d: &mut IntDev<'_>,
        u: ExprId,
        v: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let (iu, pu) = self.flatten(d, u)?;
        let (iv, pv) = self.flatten(d, v)?;
        let fu = self.fold(d, &iu);
        let fv = self.fold(d, &iv);
        let source = radd(d, u, v);
        let mid = radd(d, fu, v);
        let joined = radd(d, fu, fv);

        let step1 = rcongr(d, u, fu, pu, &|d, t| radd(d, t, v));
        let step2 = rcongr(d, v, fv, pv, &|d, t| radd(d, fu, t));
        let p12 = rtrans(d, source, mid, joined, step1, step2);

        let mut items = iu.clone();
        items.extend_from_slice(&iv);
        let target = self.fold(d, &items);
        let step3 = self.reassoc(d, &iu, &iv);
        let proof = rtrans(d, source, joined, target, p12, step3);
        Ok((items, proof))
    }

    /// `(items, proof : Eq Rat (neg e) (fold items))` — distributes `neg`
    /// fully, mirroring `super::int::Problem::flatten_neg` but using the
    /// PUBLIC `Rat.neg_neg` directly rather than an internally-derived copy.
    fn flatten_neg(
        &mut self,
        d: &mut IntDev<'_>,
        e: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let neg_e = rneg(d, e);
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head) {
            if name == p.div && !args.is_empty() {
                return Err(Decline::NonRing);
            }
            if name == d.int().rat_neg && args.len() == 1 {
                let y = args[0];
                let (items, proof_y) = self.flatten(d, y)?;
                let nn = d.const_app(p.neg_neg, &[y]);
                let folded = self.fold(d, &items);
                let full = rtrans(d, neg_e, y, folded, nn, proof_y);
                return Ok((items, full));
            }
            if name == d.int().rat_add && args.len() == 2 {
                let (u, v) = (args[0], args[1]);
                let na = d.const_app(p.neg_add, &[u, v]);
                let neg_u = rneg(d, u);
                let neg_v = rneg(d, v);
                let add_negu_negv = radd(d, neg_u, neg_v);
                let (items, proof_sum) = self.flatten_add(d, neg_u, neg_v)?;
                let folded = self.fold(d, &items);
                let full = rtrans(d, neg_e, add_negu_negv, folded, na, proof_sum);
                return Ok((items, full));
            }
            if name == d.int().rat_mul && args.len() == 2 {
                let (u, v) = (args[0], args[1]);
                let neg_v = rneg(d, v);
                let u_negv = rmul(d, u, neg_v);
                let mn = d.const_app(p.mul_neg, &[u, v]);
                let rev = rsymm(d, u_negv, neg_e, mn);
                let (items, proof_mul) = self.flatten_mul(d, u, neg_v)?;
                let folded = self.fold(d, &items);
                let full = rtrans(d, neg_e, u_negv, folded, rev, proof_mul);
                return Ok((items, full));
            }
        }
        let idx = self.atom_index(e);
        let items = vec![Item::Mono(vec![idx], true)];
        let proof = rrefl(d, neg_e);
        Ok((items, proof))
    }

    fn flatten_mul(
        &mut self,
        d: &mut IntDev<'_>,
        u: ExprId,
        v: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let (iu, pu) = self.flatten(d, u)?;
        let (iv, pv) = self.flatten(d, v)?;
        let fu = self.fold(d, &iu);
        let fv = self.fold(d, &iv);
        let source = rmul(d, u, v);
        let mid = rmul(d, fu, v);
        let joined = rmul(d, fu, fv);

        let step1 = rcongr(d, u, fu, pu, &|d, t| rmul(d, t, v));
        let step2 = rcongr(d, v, fv, pv, &|d, t| rmul(d, fu, t));
        let p12 = rtrans(d, source, mid, joined, step1, step2);

        let (dist_items, dist_proof) = self.distribute(d, &iu, &iv)?;
        let target = self.fold(d, &dist_items);
        let proof = rtrans(d, source, joined, target, p12, dist_proof);
        Ok((dist_items, proof))
    }

    fn normalize(&mut self, d: &mut IntDev<'_>, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        let (items, p1) = self.flatten(d, e)?;
        let flat = self.fold(d, &items);
        let (sorted, p2) = self.sort_items(d, &items);
        let sorted_term = self.fold(d, &sorted);
        let proof = rtrans(d, e, flat, sorted_term, p1, p2);
        Ok((sorted, proof))
    }

    fn prove_eq(
        &mut self,
        d: &mut IntDev<'_>,
        x: ExprId,
        y: ExprId,
        verify: bool,
    ) -> Result<ExprId, Decline> {
        let (ix, px) = self.normalize(d, x)?;
        let (iy, py) = self.normalize(d, y)?;
        if verify && ix != iy {
            return Err(Decline::NotAnIdentity);
        }
        let canon_x = self.fold(d, &ix);
        let canon_y = self.fold(d, &iy);
        let back = rsymm(d, y, canon_y, py);
        Ok(rtrans(d, x, canon_x, y, px, back))
    }
}

/// Wraps a raw (unsigned) `Mono*Mono` merge with each factor's sign, via the
/// public `Rat.mul_neg`/`Rat.neg_mul`/`Rat.neg_neg` — no internal derivation
/// needed, unlike `super::int::apply_mono_signs`.
#[allow(clippy::too_many_arguments)]
fn apply_mono_signs(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    sign_a: bool,
    sign_b: bool,
    raw_a: ExprId,
    raw_b: ExprId,
    raw_prod: ExprId,
    raw_proof: ExprId,
    sorted_term: ExprId,
) -> (bool, ExprId, ExprId) {
    match (sign_a, sign_b) {
        (false, false) => (false, raw_prod, raw_proof),
        (true, false) => {
            let neg_a = rneg(d, raw_a);
            let source = rmul(d, neg_a, raw_b);
            let nm = d.const_app(p.neg_mul, &[raw_a, raw_b]);
            let neg_raw_prod = rneg(d, raw_prod);
            let congr_r = rcongr(d, raw_prod, sorted_term, raw_proof, &|d, t| rneg(d, t));
            let target = rneg(d, sorted_term);
            let full = rtrans(d, source, neg_raw_prod, target, nm, congr_r);
            (true, source, full)
        }
        (false, true) => {
            let neg_b = rneg(d, raw_b);
            let source = rmul(d, raw_a, neg_b);
            let mn = d.const_app(p.mul_neg, &[raw_a, raw_b]);
            let neg_raw_prod = rneg(d, raw_prod);
            let congr_r = rcongr(d, raw_prod, sorted_term, raw_proof, &|d, t| rneg(d, t));
            let target = rneg(d, sorted_term);
            let full = rtrans(d, source, neg_raw_prod, target, mn, congr_r);
            (true, source, full)
        }
        (true, true) => {
            let neg_a = rneg(d, raw_a);
            let neg_b = rneg(d, raw_b);
            let source = rmul(d, neg_a, neg_b);
            let nm = d.const_app(p.neg_mul, &[raw_a, neg_b]);
            let mul_a_negb = rmul(d, raw_a, neg_b);
            let neg_mul_a_negb = rneg(d, mul_a_negb);
            let mn2 = d.const_app(p.mul_neg, &[raw_a, raw_b]);
            let neg_raw_prod = rneg(d, raw_prod);
            let congr2 = rcongr(d, mul_a_negb, neg_raw_prod, mn2, &|d, t| rneg(d, t));
            let neg_neg_raw_prod = rneg(d, neg_raw_prod);
            let nn = d.const_app(p.neg_neg, &[raw_prod]);
            let (_, chained) = rchain(
                d,
                source,
                &[
                    (neg_mul_a_negb, nm),
                    (neg_neg_raw_prod, congr2),
                    (raw_prod, nn),
                ],
            );
            let full = rtrans(d, source, raw_prod, sorted_term, chained, raw_proof);
            (false, source, full)
        }
    }
}

/// Prove `Eq Rat lhs rhs` from ring axioms alone, or decline.
///
/// # Errors
///
/// [`Decline`] whenever a side leaves the fragment or the two sides are not
/// (within this normalizer's completeness) the same ring expression.
pub(crate) fn prove_eq(
    d: &mut IntDev<'_>,
    prelude: &RatPrelude,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(prelude);
    problem.prove_eq(d, lhs, rhs, true)
}

/// [`prove_eq`] with the procedure's own normal-form check switched off —
/// exposed only for the corrupted-certificate tests.
///
/// # Errors
///
/// As [`prove_eq`], minus [`Decline::NotAnIdentity`].
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn prove_eq_unverified(
    d: &mut IntDev<'_>,
    prelude: &RatPrelude,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(prelude);
    problem.prove_eq(d, lhs, rhs, false)
}

/// Prove `Eq (lhs args) (rhs args)` by proving the identity generically over
/// fresh variables and instantiating at `args`.
///
/// # Errors
///
/// As [`prove_eq`], applied to the generic goal `build` states.
pub(crate) fn prove_eq_at(
    d: &mut IntDev<'_>,
    prelude: &RatPrelude,
    args: &[ExprId],
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
) -> Result<ExprId, Decline> {
    let rat_ty_ = rat_ty(d);
    let fvs: Vec<u64> = args.iter().map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (lhs, rhs) = build(d, &vars);
    let proof = prove_eq(d, prelude, lhs, rhs)?;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        value = d.lam_fv(fv, rat_ty_, value);
    }
    Ok(d.apply(value, args))
}

/// Prove `goal` (`Eq Rat _ _`) from ring axioms alone, or decline.
///
/// # Errors
///
/// [`Decline::GoalNotAtomic`] when `goal`'s head is not `Eq` at `Rat`;
/// otherwise as [`prove_eq`].
pub(crate) fn prove(
    d: &mut IntDev<'_>,
    prelude: &RatPrelude,
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(prelude);
    let (lhs, rhs) = problem.parse_eq_goal(d, goal)?;
    problem.prove_eq(d, lhs, rhs, true)
}

/// Why [`theorem`] produced no declaration.
#[derive(Debug)]
pub(crate) enum RingError {
    /// The procedure declined.
    Declined(Decline),
    /// The procedure emitted a term and the **kernel** refused it.
    Rejected(crate::KernelError),
}

impl core::fmt::Display for RingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Declined(d) => write!(f, "ring declined: {d:?}"),
            Self::Rejected(e) => write!(f, "kernel rejected the emitted term: {e:?}"),
        }
    }
}

/// Declare `theorem name : ∀ x₀ … x_{arity−1}, concl`, with `build`
/// returning the (unconditional, ring-only) conclusion and the proof
/// searched for and emitted, never written by hand.
///
/// # Errors
///
/// [`RingError::Declined`] when the procedure found no term, or
/// [`RingError::Rejected`] when the kernel refused the one it found.
pub(crate) fn theorem(
    d: &mut IntDev<'_>,
    prelude: &RatPrelude,
    name: crate::NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> Result<ExprId, RingError> {
    let rat_ty_ = rat_ty(d);
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let concl = build(d, &vars);

    let proof = prove(d, prelude, concl).map_err(RingError::Declined)?;

    let mut ty = concl;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, rat_ty_, ty);
        value = d.lam_fv(fv, rat_ty_, value);
    }
    d.declare_theorem(name, ty, value)
        .map_err(RingError::Rejected)?;
    Ok(ty)
}

/// [`theorem`], with the outcome collapsed into the prelude build's own
/// error channel.
///
/// # Errors
///
/// The kernel's rejection when the emitted term was refused, or
/// `UnknownConst { name }` when the search declined and no term was built.
pub(crate) fn declare(
    d: &mut IntDev<'_>,
    prelude: &RatPrelude,
    name: crate::NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> Result<(), crate::KernelError> {
    match theorem(d, prelude, name, arity, build) {
        Ok(_) => Ok(()),
        Err(RingError::Rejected(e)) => Err(e),
        Err(RingError::Declined(_)) => Err(crate::KernelError::UnknownConst { name }),
    }
}

#[cfg(test)]
mod tests;
