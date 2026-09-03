//! The ℤ fragment: parse `ExprId`s into a canonical **signed** sum of
//! monomials, and emit a kernel proof term for `t₁ = t₂` when the two sides
//! agree — the same shape as [`super::nat`], forced into a different design
//! by the carrier ([`crate::int_prelude::ops::IntDev`], ADR-1582).
//!
//! ## What differs from [`super::nat`]
//!
//! - **`neg`/`sub` are ring operations here**, not declined. `Int.sub a b`
//!   is a plain `Definition := add a (neg b)`, so it flattens by delta-defeq
//!   exactly the way `Nat.succ` flattens by iota over there. `neg` of a
//!   compound distributes fully (`neg_add` over `+`, `mul_neg` over `*`,
//!   an internally-derived `neg_neg` over `neg`) rather than being treated as
//!   an opaque atom the way `linarith::int` treats it — this producer needs
//!   the full distribution to retire the identities it targets.
//! - **Nothing reduces.** `Int.add`/`Int.mul` case-split on both arguments
//!   (`docs/contributor-guide/kernel-proof-engineering.md`), so `nat.rs`'s
//!   `scale_item` trick (bridging a numeral-coefficient unroll with `d.refl`
//!   over `Nat.mul`'s own iota-reduction) does not transfer: this module's
//!   `scale_unsigned` builds the same unroll by genuine `left_distrib`
//!   induction, splitting `ofNat (i+1) = ofNat i + ofNat 1` by a **closed**
//!   iota/delta reduction (both sides concrete numerals) at each step.
//! - **Items carry an explicit sign** (`Item::Mono(Vec<usize>, bool)`,
//!   `Item::Num(Coeff)` already signed) rather than nat.rs's unsigned
//!   repeat-count convention, because ℤ coefficients and monomial factors can
//!   be negative and there is no free reduction to fold a sign into.
//!
//! ## What is shared with [`super::nat`]
//!
//! The outer sum's re-association/sorting (`reassoc`, `sort_items`) and a
//! monomial's own factor sorting (`sort_factors`, ring-tactic-2) are the same
//! three-step `assoc`/`comm`/`symm(assoc)` adjacent-transposition trick,
//! ported to `Int.add`/`Int.mul` and `IntPrelude`'s `add_assoc`/`add_comm`/
//! `mul_assoc`/`mul_comm`.
//!
//! ## Lemma table
//!
//! | lemma | role |
//! | --- | --- |
//! | `Int.add_assoc` / `Int.add_comm` | the outer sum's normalizer |
//! | `Int.mul_assoc` | merging two monomials' factor lists |
//! | `Int.mul_comm` | flipping a numeral coefficient, and factor sorting |
//! | `Int.left_distrib` | distributing a single monomial over a sum |
//! | `Int.add_mul` | distributing a sum over a single monomial (ℤ's `right_distrib`) |
//! | `Int.neg_add` | distributing `neg` over a sum |
//! | `Int.mul_neg` | distributing `neg` out of the right factor of a product |
//! | `Int.mul_zero` / `Int.mul_one` / `Int.one_mul` | numeral-coefficient base cases |
//! | `Int.neg_one_mul` | the derived `neg_neg`/`neg_mul` helpers' base |
//!
//! `neg_mul` (`(neg a)*c = neg(a*c)`) and `neg_neg` (`neg(neg x) = x`) are
//! **not** in `IntPrelude` as public theorems reachable from here — both are
//! retirement targets of this very producer (`int_prelude/gcd.rs` and
//! `int_prelude/fibonacci.rs` each hand-derive a private copy of `neg_neg`)
//! — so this module derives them once, internally, from `mul_comm`/
//! `mul_neg`/`neg_one_mul`/`mul_assoc`/`one_mul` alone, the same
//! "can't retire a producer's own primitive" lesson ADR-1580 recorded for
//! `add_right_comm`.

use crate::ExprNode;
use crate::IntPrelude;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

use super::{Coeff, Decline, MAX_COEFF};

/// One summand of a canonical additive form over ℤ: a signed monomial (a
/// left-to-right, **sorted** factor list — see the module docs) or a signed
/// numeral.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Item {
    /// Atom-table indices, sorted ascending, plus whether the whole product
    /// is negated.
    Mono(Vec<usize>, bool),
    /// A signed literal `Int` numeral.
    Num(Coeff),
}

impl Item {
    /// Sort key: monomials before numerals; a monomial compares by its
    /// (already-sorted) factor list, then sign.
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

/// The parsing/emission context for one ℤ goal.
struct Problem {
    prelude: IntPrelude,
    atoms: Vec<ExprId>,
}

impl Problem {
    fn new(prelude: &IntPrelude) -> Self {
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

    // --- parsing --------------------------------------------------------

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

    /// `e` as a `Nat` numeral `succ^k zero`.
    fn nat_numeral(&self, d: &mut IntDev<'_>, e: ExprId) -> Option<Coeff> {
        let nat = self.prelude.nat;
        let mut current = e;
        let mut count: Coeff = 0;
        loop {
            match d.kernel().expr_node(current).clone() {
                ExprNode::Const(n, _) if n == nat.zero => return Some(count),
                ExprNode::App(f, a) => match d.kernel().expr_node(f).clone() {
                    ExprNode::Const(n, _) if n == nat.succ => {
                        count = count.checked_add(1)?;
                        current = a;
                    }
                    _ => return None,
                },
                _ => return None,
            }
        }
    }

    /// `e` as a literal integer, `linarith::int::Problem::int_numeral`'s
    /// exact recognizer (zero, one, `ofNat`, `negSucc`, or `neg` of any of
    /// those).
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
        if name == p.of_nat && args.len() == 1 {
            return self.nat_numeral(d, args[0]);
        }
        if name == p.neg_succ && args.len() == 1 {
            return self.nat_numeral(d, args[0]).map(|k| -(k + 1));
        }
        if name == p.neg && args.len() == 1 {
            return self.as_numeral(d, args[0]).map(|k| -k);
        }
        None
    }

    /// `Eq Int lhs rhs`, unpacked.
    ///
    /// # Errors
    ///
    /// [`Decline::GoalNotAtomic`] when the head is not `Eq` at `Int`.
    fn parse_eq_goal(
        &mut self,
        d: &mut IntDev<'_>,
        e: ExprId,
    ) -> Result<(ExprId, ExprId), Decline> {
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        let name = Self::head_const(d, head).ok_or(Decline::GoalNotAtomic)?;
        if name == p.logic.eq && args.len() == 3 {
            let int_ty = d.int_ty();
            if args[0] == int_ty {
                return Ok((args[1], args[2]));
            }
        }
        Err(Decline::GoalNotAtomic)
    }

    // --- term builders ----------------------------------------------------

    /// `0`/`1`/`ofNat k` — the canonical unsigned-numeral spelling.
    fn build_numeral(d: &mut IntDev<'_>, k: u32) -> ExprId {
        if k == 0 {
            d.izero()
        } else if k == 1 {
            d.ione()
        } else {
            let n = d.num(k);
            d.of_nat(n)
        }
    }

    fn build_numeral_signed(d: &mut IntDev<'_>, k: Coeff) -> ExprId {
        if k >= 0 {
            Self::build_numeral(d, u32::try_from(k).unwrap_or(0))
        } else {
            let mag = u32::try_from(-k).unwrap_or(0);
            let base = Self::build_numeral(d, mag);
            d.ineg(base)
        }
    }

    fn item_term(&self, d: &mut IntDev<'_>, item: &Item) -> ExprId {
        match item {
            Item::Mono(vars, neg) => {
                let base = self.fold_mul(d, vars);
                if *neg { d.ineg(base) } else { base }
            }
            Item::Num(k) => Self::build_numeral_signed(d, *k),
        }
    }

    fn fold(&self, d: &mut IntDev<'_>, items: &[Item]) -> ExprId {
        let mut acc = self.item_term(d, &items[0]);
        for item in &items[1..] {
            let t = self.item_term(d, item);
            acc = d.iadd(acc, t);
        }
        acc
    }

    fn fold_from(&self, d: &mut IntDev<'_>, start: ExprId, items: &[Item]) -> ExprId {
        let mut acc = start;
        for item in items {
            let t = self.item_term(d, item);
            acc = d.iadd(acc, t);
        }
        acc
    }

    fn fold_mul(&self, d: &mut IntDev<'_>, vars: &[usize]) -> ExprId {
        let mut acc = self.atoms[vars[0]];
        for &v in &vars[1..] {
            let t = self.atoms[v];
            acc = d.imul(acc, t);
        }
        acc
    }

    fn fold_mul_from(&self, d: &mut IntDev<'_>, start: ExprId, vars: &[usize]) -> ExprId {
        let mut acc = start;
        for &v in vars {
            let t = self.atoms[v];
            acc = d.imul(acc, t);
        }
        acc
    }

    // --- outer-sum re-association / sorting (mirrors `nat::Problem`) ------

    fn reassoc(&self, d: &mut IntDev<'_>, left: &[Item], right: &[Item]) -> ExprId {
        let fl = self.fold(d, left);
        if right.len() == 1 {
            let joined = self.fold_from(d, fl, right);
            return d.irefl(joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, &last[0]);
        let fr = d.iadd(fi, last_t);
        let p = d.int();

        let source = d.iadd(fl, fr);
        let regrouped_inner = d.iadd(fl, fi);
        let regrouped = d.iadd(regrouped_inner, last_t);
        let assoc = d.const_app(p.add_assoc, &[fl, fi, last_t]);
        let step1 = d.isymm(regrouped, source, assoc);

        let inner = self.reassoc(d, left, init);
        let mut joined_items = left.to_vec();
        joined_items.extend_from_slice(init);
        let joined_inner = self.fold(d, &joined_items);
        let step2 = d.icongr(regrouped_inner, joined_inner, inner, &|d, x| {
            d.iadd(x, last_t)
        });
        let target = d.iadd(joined_inner, last_t);
        d.itrans(source, regrouped, target, step1, step2)
    }

    fn reassoc_mul(&self, d: &mut IntDev<'_>, left: &[usize], right: &[usize]) -> ExprId {
        let fl = self.fold_mul(d, left);
        if right.len() == 1 {
            let joined = d.imul(fl, self.atoms[right[0]]);
            return d.irefl(joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold_mul(d, init);
        let last_t = self.atoms[last[0]];
        let fr = d.imul(fi, last_t);
        let p = d.int();

        let source = d.imul(fl, fr);
        let regrouped_inner = d.imul(fl, fi);
        let regrouped = d.imul(regrouped_inner, last_t);
        let assoc = d.const_app(p.mul_assoc, &[fl, fi, last_t]);
        let step1 = d.isymm(regrouped, source, assoc);

        let inner = self.reassoc_mul(d, left, init);
        let mut joined_vars = left.to_vec();
        joined_vars.extend_from_slice(init);
        let joined_inner = self.fold_mul(d, &joined_vars);
        let step2 = d.icongr(regrouped_inner, joined_inner, inner, &|d, x| {
            d.imul(x, last_t)
        });
        let target = d.imul(joined_inner, last_t);
        d.itrans(source, regrouped, target, step1, step2)
    }

    /// Sort a monomial's factor list into canonical (index) order — the
    /// multiplicative twin of [`Self::sort_items`], `nat::Problem`'s
    /// `sort_factors` ported to `Int`.
    fn sort_factors(&self, d: &mut IntDev<'_>, vars: &[usize]) -> (Vec<usize>, ExprId) {
        let source = self.fold_mul(d, vars);
        let mut current: Vec<usize> = vars.to_vec();
        let mut proof = d.irefl(source);
        let mut folded = source;
        loop {
            let mut swapped = false;
            for k in 0..current.len().saturating_sub(1) {
                if current[k] <= current[k + 1] {
                    continue;
                }
                let p = d.int();
                let x = self.atoms[current[k]];
                let y = self.atoms[current[k + 1]];
                let (inner_before, inner_after, base) = if k == 0 {
                    let before = d.imul(x, y);
                    let after = d.imul(y, x);
                    let lemma = d.const_app(p.mul_comm, &[x, y]);
                    (before, after, lemma)
                } else {
                    let prefix = self.fold_mul(d, &current[..k]);
                    let before_inner = d.imul(prefix, x);
                    let before = d.imul(before_inner, y);
                    let xy = d.imul(x, y);
                    let assoc1 = d.const_app(p.mul_assoc, &[prefix, x, y]);
                    let mid1 = d.imul(prefix, xy);
                    let comm = d.const_app(p.mul_comm, &[x, y]);
                    let yx = d.imul(y, x);
                    let step2 = d.icongr(xy, yx, comm, &|d, t| d.imul(prefix, t));
                    let mid2 = d.imul(prefix, yx);
                    let after_inner = d.imul(prefix, y);
                    let after = d.imul(after_inner, x);
                    let assoc2 = d.const_app(p.mul_assoc, &[prefix, y, x]);
                    let step3 = d.isymm(after, mid2, assoc2);
                    let (_, base) =
                        d.ichain(before, &[(mid1, assoc1), (mid2, step2), (after, step3)]);
                    (before, after, base)
                };
                let tail = current[k + 2..].to_vec();
                let step = d.icongr(inner_before, inner_after, base, &|d, t| {
                    self.fold_mul_from(d, t, &tail)
                });
                current.swap(k, k + 1);
                let next = self.fold_mul(d, &current);
                proof = d.itrans(source, folded, next, proof, step);
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
        let mut proof = d.irefl(source);
        let mut folded = source;
        loop {
            let mut swapped = false;
            for k in 0..current.len().saturating_sub(1) {
                if current[k].key() <= current[k + 1].key() {
                    continue;
                }
                let p = d.int();
                let x = self.item_term(d, &current[k]);
                let y = self.item_term(d, &current[k + 1]);
                let (inner_before, inner_after, base) = if k == 0 {
                    let before = d.iadd(x, y);
                    let after = d.iadd(y, x);
                    let lemma = d.const_app(p.add_comm, &[x, y]);
                    (before, after, lemma)
                } else {
                    let prefix = self.fold(d, &current[..k]);
                    let before_inner = d.iadd(prefix, x);
                    let before = d.iadd(before_inner, y);
                    let xy = d.iadd(x, y);
                    let assoc1 = d.const_app(p.add_assoc, &[prefix, x, y]);
                    let mid1 = d.iadd(prefix, xy);
                    let comm = d.const_app(p.add_comm, &[x, y]);
                    let yx = d.iadd(y, x);
                    let step2 = d.icongr(xy, yx, comm, &|d, t| d.iadd(prefix, t));
                    let mid2 = d.iadd(prefix, yx);
                    let after_inner = d.iadd(prefix, y);
                    let after = d.iadd(after_inner, x);
                    let assoc2 = d.const_app(p.add_assoc, &[prefix, y, x]);
                    let step3 = d.isymm(after, mid2, assoc2);
                    let (_, base) =
                        d.ichain(before, &[(mid1, assoc1), (mid2, step2), (after, step3)]);
                    (before, after, base)
                };
                let tail = current[k + 2..].to_vec();
                let step = d.icongr(inner_before, inner_after, base, &|d, t| {
                    self.fold_from(d, t, &tail)
                });
                current.swap(k, k + 1);
                let next = self.fold(d, &current);
                proof = d.itrans(source, folded, next, proof, step);
                folded = next;
                swapped = true;
            }
            if !swapped {
                break;
            }
        }
        (current, proof)
    }

    // --- internally-derived primitives: `neg_neg`, `neg_mul` -------------

    /// `Eq Int (neg (neg x)) x`, derived from `neg_one_mul`/`mul_assoc`/
    /// `one_mul` alone — `int_prelude/gcd.rs`'s private `neg_neg`'s exact
    /// derivation, kept here rather than depended on (see module docs).
    fn neg_neg_lemma(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
        let p = d.int();
        let one_c = d.ione();
        let neg_one = d.ineg(one_c);
        let neg_x = d.ineg(x);
        let neg_neg_x = d.ineg(neg_x);

        let mul_negone_negx = d.imul(neg_one, neg_x);
        let step1 = {
            let fwd = d.const_app(p.neg_one_mul, &[neg_x]);
            d.isymm(mul_negone_negx, neg_neg_x, fwd)
        };

        let inner = d.imul(neg_one, x);
        let step2 = {
            let fwd = d.const_app(p.neg_one_mul, &[x]);
            let negx_eq = d.isymm(inner, neg_x, fwd);
            d.icongr(neg_x, inner, negx_eq, &|d, y| d.imul(neg_one, y))
        };
        let mul_negone_inner = d.imul(neg_one, inner);

        let negone_sq = d.imul(neg_one, neg_one);
        let step3 = {
            let fwd = d.const_app(p.mul_assoc, &[neg_one, neg_one, x]);
            let lhs = d.imul(negone_sq, x);
            d.isymm(lhs, mul_negone_inner, fwd)
        };
        let negone_sq_x = d.imul(negone_sq, x);

        let negone_sq_eq_one = {
            let fwd = d.const_app(p.neg_one_mul, &[neg_one]);
            let neg_neg_one = d.ineg(neg_one);
            let neg_neg_one_pf = d.irefl(one_c);
            d.itrans(negone_sq, neg_neg_one, one_c, fwd, neg_neg_one_pf)
        };
        let step5 = d.icongr(negone_sq, one_c, negone_sq_eq_one, &|d, y| d.imul(y, x));
        let one_x = d.imul(one_c, x);
        let step6 = d.const_app(p.one_mul, &[x]);

        let (_, chained) = d.ichain(
            neg_neg_x,
            &[
                (mul_negone_negx, step1),
                (mul_negone_inner, step2),
                (negone_sq_x, step3),
                (one_x, step5),
                (x, step6),
            ],
        );
        chained
    }

    /// `Eq Int (mul (neg a) c) (neg (mul a c))`, derived from `mul_comm`
    /// (twice) and the public `mul_neg` — three steps, shorter than
    /// `int_prelude/gcd.rs`'s own private copy.
    fn neg_mul_lemma(d: &mut IntDev<'_>, a: ExprId, c: ExprId) -> ExprId {
        let p = d.int();
        let neg_a = d.ineg(a);
        let start = d.imul(neg_a, c);
        let ca = d.imul(c, neg_a);
        let s1 = d.const_app(p.mul_comm, &[neg_a, c]);

        let ac = d.imul(a, c);
        let neg_ac = d.ineg(ac);
        let s2 = d.const_app(p.mul_neg, &[c, a]);
        let ca_prime = d.imul(c, a);
        let neg_ca = d.ineg(ca_prime);
        let comm2 = d.const_app(p.mul_comm, &[c, a]);
        let s3 = d.icongr(ca_prime, ac, comm2, &|d, t| d.ineg(t));

        let (_, proof) = d.ichain(start, &[(ca, s1), (neg_ca, s2), (neg_ac, s3)]);
        proof
    }

    /// `Eq Int (neg (fold items)) (fold negated_items)` — distributes `neg`
    /// over a whole additive fold, one `neg_add` per join.
    fn negate_fold(&self, d: &mut IntDev<'_>, items: &[Item]) -> (Vec<Item>, ExprId) {
        if items.len() == 1 {
            let negated = vec![items[0].negated()];
            let proof = self.neg_item_proof(d, &items[0]);
            return (negated, proof);
        }
        let p = d.int();
        let (init, last) = items.split_at(items.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, &last[0]);
        let source = d.iadd(fi, last_t);
        let neg_source = d.ineg(source);

        let neg_fi = d.ineg(fi);
        let neg_last = d.ineg(last_t);
        let na = d.const_app(p.neg_add, &[fi, last_t]);
        let sum_neg = d.iadd(neg_fi, neg_last);

        let (init_neg, proof_init) = self.negate_fold(d, init);
        let last_neg = last[0].negated();
        let proof_last = self.neg_item_proof(d, &last[0]);

        let target_init = self.fold(d, &init_neg);
        let target_last = self.item_term(d, &last_neg);
        let step_a = d.icongr(neg_fi, target_init, proof_init, &|d, t| d.iadd(t, neg_last));
        let mid2 = d.iadd(target_init, neg_last);
        let step_b = d.icongr(neg_last, target_last, proof_last, &|d, t| {
            d.iadd(target_init, t)
        });
        let mid3 = d.iadd(target_init, target_last);
        let step_ab = d.itrans(sum_neg, mid2, mid3, step_a, step_b);

        let (_, full) = d.ichain(neg_source, &[(sum_neg, na), (mid3, step_ab)]);
        let mut new_items = init_neg;
        new_items.push(last_neg);
        (new_items, full)
    }

    /// `Eq Int (neg (item_term item)) (item_term item.negated())`.
    fn neg_item_proof(&self, d: &mut IntDev<'_>, item: &Item) -> ExprId {
        let t = self.item_term(d, item);
        let neg_t = d.ineg(t);
        match item {
            Item::Mono(_, false) => d.irefl(neg_t),
            Item::Mono(vars, true) => {
                let base = self.fold_mul(d, vars);
                Self::neg_neg_lemma(d, base)
            }
            Item::Num(k) if *k > 0 => d.irefl(neg_t),
            Item::Num(k) if *k < 0 => {
                let mag = u32::try_from(k.unsigned_abs()).unwrap_or(0);
                let base = Self::build_numeral(d, mag);
                Self::neg_neg_lemma(d, base)
            }
            Item::Num(_) => {
                // k == 0: `neg zero = zero`, via `neg_one_mul`/`mul_zero`.
                let p = d.int();
                let zero = d.izero();
                let neg_zero = d.ineg(zero);
                let one_c = d.ione();
                let neg_one = d.ineg(one_c);
                let mul_negone_zero = d.imul(neg_one, zero);
                let step1 = {
                    let fwd = d.const_app(p.neg_one_mul, &[zero]);
                    d.isymm(mul_negone_zero, neg_zero, fwd)
                };
                let step2 = d.const_app(p.mul_zero, &[neg_one]);
                d.itrans(neg_zero, mul_negone_zero, zero, step1, step2)
            }
        }
    }

    // --- the multiplicative unroll (a numeral coefficient) --------------

    /// `Eq Int (mul it (numeral mag)) (fold mag_items)`, `mag_items` being
    /// `mag` unchanged copies of `item` — genuine `left_distrib` induction
    /// (see module docs), not the ℕ ι-reduction bridge.
    fn scale_unsigned(&mut self, d: &mut IntDev<'_>, item: &Item, mag: i64) -> (Vec<Item>, ExprId) {
        let p = d.int();
        let it = self.item_term(d, item);
        if mag == 0 {
            // `mul it zero = zero` directly — no accumulator, and crucially
            // no phantom leading `Item::Num(0)` surviving into a nonempty
            // result the way seeding the loop at `prev_num = 0` would leave
            // one (`sort_items` would then move it to the tail, and a clean
            // RHS with no such summand would mismatch it — the bug this
            // early-return and the `mag == 1` seed below fix).
            let items = vec![Item::Num(0)];
            let proof = d.const_app(p.mul_zero, &[it]);
            return (items, proof);
        }
        // Seed the induction at `mag == 1`, not `mag == 0`: the item list
        // starts with one real copy of `item`, never a placeholder constant.
        let mut current_items: Vec<Item> = vec![item.clone()];
        let mut current = it;
        let mut proof = d.const_app(p.mul_one, &[it]);
        let mut prev_num = Self::build_numeral(d, 1);
        let mut i: i64 = 1;
        while i < mag {
            i += 1;
            let one = d.ione();
            let next_num = Self::build_numeral(d, u32::try_from(i).unwrap_or(0));
            let split_target = d.iadd(prev_num, one);
            let mul_it_split = d.imul(it, split_target);
            let mul_it_prev = d.imul(it, prev_num);
            let mul_it_one = d.imul(it, one);
            let ld = d.const_app(p.left_distrib, &[it, prev_num, one]);
            let sum = d.iadd(mul_it_prev, mul_it_one);

            let mo = d.const_app(p.mul_one, &[it]);
            let step_a = d.icongr(mul_it_prev, current, proof, &|d, t| d.iadd(t, mul_it_one));
            let mid = d.iadd(current, mul_it_one);
            let step_b = d.icongr(mul_it_one, it, mo, &|d, t| d.iadd(current, t));

            let mut next_items = current_items.clone();
            next_items.push(item.clone());
            let next = self.fold(d, &next_items);

            let (_, chained) = d.ichain(mul_it_split, &[(sum, ld), (mid, step_a), (next, step_b)]);
            let mul_it_next_num = d.imul(it, next_num);
            let bridge = d.irefl(mul_it_split);
            proof = d.itrans(mul_it_next_num, mul_it_split, next, bridge, chained);

            current = next;
            current_items = next_items;
            prev_num = next_num;
        }
        (current_items, proof)
    }

    /// `Eq Int (mul (item_term item) (numeral count)) (fold result)`, or —
    /// with `commuted` — `Eq Int (mul (numeral count) (item_term item))
    /// (fold result)`. `count` may be negative; the sign is wrapped around
    /// [`Self::scale_unsigned`]'s unsigned result via `mul_neg`/
    /// [`Self::neg_mul_lemma`] and [`Self::negate_fold`].
    fn scale_item(
        &mut self,
        d: &mut IntDev<'_>,
        item: &Item,
        count: Coeff,
        commuted: bool,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        if count.unsigned_abs() > MAX_COEFF.unsigned_abs() {
            return Err(Decline::CoefficientTooLarge);
        }
        // `count.unsigned_abs() <= MAX_COEFF` (checked above) bounds `count`
        // well inside `i64`, so `abs()` cannot panic here.
        let mag = count.abs();
        let neg_result = count < 0;
        let it = self.item_term(d, item);
        let (mag_items, mag_proof) = self.scale_unsigned(d, item, mag);
        let mag_num = Self::build_numeral(d, u32::try_from(mag).unwrap_or(0));
        let p = d.int();

        let (base_items, base_proof, base_lhs) = if neg_result {
            let neg_mag_num = d.ineg(mag_num);
            let mul_it_negmag = d.imul(it, neg_mag_num);
            let mul_it_mag = d.imul(it, mag_num);
            let mn = d.const_app(p.mul_neg, &[it, mag_num]);
            let neg_mul_it_mag = d.ineg(mul_it_mag);
            let mag_folded = self.fold(d, &mag_items);
            let congr_mag = d.icongr(mul_it_mag, mag_folded, mag_proof, &|d, t| d.ineg(t));
            let (neg_items, negf_proof) = self.negate_fold(d, &mag_items);
            let target = self.fold(d, &neg_items);
            let neg_folded = d.ineg(mag_folded);
            let (_, chained) = d.ichain(
                mul_it_negmag,
                &[
                    (neg_mul_it_mag, mn),
                    (neg_folded, congr_mag),
                    (target, negf_proof),
                ],
            );
            (neg_items, chained, mul_it_negmag)
        } else {
            (mag_items, mag_proof, d.imul(it, mag_num))
        };

        if commuted {
            let factor_num = if neg_result { d.ineg(mag_num) } else { mag_num };
            let commuted_lhs = d.imul(factor_num, it);
            let comm = d.const_app(p.mul_comm, &[factor_num, it]);
            let target = self.fold(d, &base_items);
            let full = d.itrans(commuted_lhs, base_lhs, target, comm, base_proof);
            Ok((base_items, full))
        } else {
            Ok((base_items, base_proof))
        }
    }

    /// `Eq Int (mul (item_term a) (item_term b)) (fold result)`.
    fn combine_items(
        &mut self,
        d: &mut IntDev<'_>,
        a: &Item,
        b: &Item,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        match (a, b) {
            (Item::Num(x), Item::Num(y)) => {
                let prod = x.checked_mul(*y).ok_or(Decline::CoefficientTooLarge)?;
                if prod.unsigned_abs() > (MAX_COEFF * MAX_COEFF).unsigned_abs() {
                    return Err(Decline::CoefficientTooLarge);
                }
                let xa = self.item_term(d, a);
                let yb = self.item_term(d, b);
                let source = d.imul(xa, yb);
                let target_item = Item::Num(prod);
                let target = self.item_term(d, &target_item);
                // Two concrete numerals (up to sign, wholly closed): the
                // full delta/iota reduction chain terminates at the same
                // literal regardless of spelling.
                let proof = d.irefl(target);
                let _ = source;
                Ok((vec![target_item], proof))
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
                let raw_prod = d.imul(raw_a, raw_b);
                let raw_proof = d.itrans(raw_prod, merged_term, sorted_term, reassoc, sort_proof);

                let raw = RawMerge {
                    a: raw_a,
                    b: raw_b,
                    prod: raw_prod,
                    proof: raw_proof,
                    sorted: sorted_term,
                };
                let (result_sign, source, proof) = apply_mono_signs(d, *sign_a, *sign_b, raw);
                let _ = source;
                Ok((vec![Item::Mono(sorted, result_sign)], proof))
            }
        }
    }
}

/// The raw (unsigned) merge of two monomials' factor lists — `prod = mul a
/// b`, `proof : Eq Int prod sorted`, `sorted` the sorted merged factor
/// list's term. Bundled to keep [`apply_mono_signs`] under the arity lint.
#[derive(Clone, Copy)]
struct RawMerge {
    a: ExprId,
    b: ExprId,
    prod: ExprId,
    proof: ExprId,
    sorted: ExprId,
}

/// Wraps a [`RawMerge`] with each original factor's sign, returning
/// `(result_sign, source, proof)` where `source = mul (item_term
/// (Mono(_,sign_a))) (item_term (Mono(_,sign_b)))` and `proof : Eq Int
/// source (if result_sign {neg raw.sorted} else {raw.sorted})`.
fn apply_mono_signs(
    d: &mut IntDev<'_>,
    sign_a: bool,
    sign_b: bool,
    raw: RawMerge,
) -> (bool, ExprId, ExprId) {
    let p = d.int();
    let RawMerge {
        a: raw_a,
        b: raw_b,
        prod: raw_prod,
        proof: raw_proof,
        sorted: sorted_term,
    } = raw;
    match (sign_a, sign_b) {
        (false, false) => (false, raw_prod, raw_proof),
        (true, false) => {
            let neg_a = d.ineg(raw_a);
            let source = d.imul(neg_a, raw_b);
            let nm = Problem::neg_mul_lemma(d, raw_a, raw_b);
            let neg_raw_prod = d.ineg(raw_prod);
            let congr_r = d.icongr(raw_prod, sorted_term, raw_proof, &|d, t| d.ineg(t));
            let target = d.ineg(sorted_term);
            let full = d.itrans(source, neg_raw_prod, target, nm, congr_r);
            (true, source, full)
        }
        (false, true) => {
            let neg_b = d.ineg(raw_b);
            let source = d.imul(raw_a, neg_b);
            let mn = d.const_app(p.mul_neg, &[raw_a, raw_b]);
            let neg_raw_prod = d.ineg(raw_prod);
            let congr_r = d.icongr(raw_prod, sorted_term, raw_proof, &|d, t| d.ineg(t));
            let target = d.ineg(sorted_term);
            let full = d.itrans(source, neg_raw_prod, target, mn, congr_r);
            (true, source, full)
        }
        (true, true) => {
            let neg_a = d.ineg(raw_a);
            let neg_b = d.ineg(raw_b);
            let source = d.imul(neg_a, neg_b);
            let nm = Problem::neg_mul_lemma(d, raw_a, neg_b);
            let mul_a_negb = d.imul(raw_a, neg_b);
            let neg_mul_a_negb = d.ineg(mul_a_negb);
            let mn2 = d.const_app(p.mul_neg, &[raw_a, raw_b]);
            let neg_raw_prod = d.ineg(raw_prod);
            let congr2 = d.icongr(mul_a_negb, neg_raw_prod, mn2, &|d, t| d.ineg(t));
            let neg_neg_raw_prod = d.ineg(neg_raw_prod);
            let nn = Problem::neg_neg_lemma(d, raw_prod);
            let (_, chained) = d.ichain(
                source,
                &[
                    (neg_mul_a_negb, nm),
                    (neg_neg_raw_prod, congr2),
                    (raw_prod, nn),
                ],
            );
            let full = d.itrans(source, raw_prod, sorted_term, chained, raw_proof);
            (false, source, full)
        }
    }
}

impl Problem {
    /// `Eq Int (mul (item_term item) (fold iv)) (fold result)`.
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
        let fv = d.iadd(fi, last_t);
        let it = self.item_term(d, item);
        let source = d.imul(it, fv);

        let mul_it_fi = d.imul(it, fi);
        let mul_it_last = d.imul(it, last_t);
        let sum = d.iadd(mul_it_fi, mul_it_last);
        let p = d.int();
        let ld = d.const_app(p.left_distrib, &[it, fi, last_t]);

        let (items_init, proof_init) = self.distribute_single(d, item, init)?;
        let (items_last, proof_last) = self.combine_items(d, item, &last[0])?;
        let target_init = self.fold(d, &items_init);
        let target_last = self.fold(d, &items_last);
        let step_a = d.icongr(mul_it_fi, target_init, proof_init, &|d, t| {
            d.iadd(t, mul_it_last)
        });
        let mid2 = d.iadd(target_init, mul_it_last);
        let step_b = d.icongr(mul_it_last, target_last, proof_last, &|d, t| {
            d.iadd(target_init, t)
        });
        let mid3 = d.iadd(target_init, target_last);
        let step_ab = d.itrans(sum, mid2, mid3, step_a, step_b);

        let mut items = items_init.clone();
        items.extend_from_slice(&items_last);
        let combined = self.fold(d, &items);
        let reassoc = self.reassoc(d, &items_init, &items_last);
        let joined_proof = d.itrans(sum, mid3, combined, step_ab, reassoc);
        let full = d.itrans(source, sum, combined, ld, joined_proof);
        Ok((items, full))
    }

    /// `Eq Int (mul (fold iu) (fold iv)) (fold result)`, via `Int.add_mul`
    /// (ℤ's `right_distrib`) peeling one summand at a time.
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
        let fu = d.iadd(fi, last_t);
        let fv = self.fold(d, iv);
        let source = d.imul(fu, fv);

        let mul_fi_fv = d.imul(fi, fv);
        let mul_last_fv = d.imul(last_t, fv);
        let sum = d.iadd(mul_fi_fv, mul_last_fv);
        let p = d.int();
        let rd = d.const_app(p.add_mul, &[fi, last_t, fv]);

        let (items_init, proof_init) = self.distribute(d, init, iv)?;
        let (items_last, proof_last) = self.distribute_single(d, &last[0], iv)?;
        let target_init = self.fold(d, &items_init);
        let target_last = self.fold(d, &items_last);
        let step_a = d.icongr(mul_fi_fv, target_init, proof_init, &|d, t| {
            d.iadd(t, mul_last_fv)
        });
        let mid2 = d.iadd(target_init, mul_last_fv);
        let step_b = d.icongr(mul_last_fv, target_last, proof_last, &|d, t| {
            d.iadd(target_init, t)
        });
        let mid3 = d.iadd(target_init, target_last);
        let step_ab = d.itrans(sum, mid2, mid3, step_a, step_b);

        let mut items = items_init.clone();
        items.extend_from_slice(&items_last);
        let combined = self.fold(d, &items);
        let reassoc = self.reassoc(d, &items_init, &items_last);
        let joined_proof = d.itrans(sum, mid3, combined, step_ab, reassoc);
        let full = d.itrans(source, sum, combined, rd, joined_proof);
        Ok((items, full))
    }

    // --- flatten: source term -> raw item list ---------------------------

    /// `(items, proof : Eq Int e (fold items))`.
    ///
    /// # Errors
    ///
    /// [`Decline::NonRing`] for `ediv`/`emod`; [`Decline::CoefficientTooLarge`]
    /// from the multiplicative unroll.
    fn flatten(&mut self, d: &mut IntDev<'_>, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        if let Some(k) = self.as_numeral(d, e) {
            let items = vec![Item::Num(k)];
            let folded = self.fold(d, &items);
            let proof = d.irefl(folded);
            return Ok((items, proof));
        }
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head) {
            if (name == p.ediv || name == p.emod) && !args.is_empty() {
                return Err(Decline::NonRing);
            }
            if name == p.add && args.len() == 2 {
                return self.flatten_add(d, args[0], args[1]);
            }
            if name == p.sub && args.len() == 2 {
                let negb = d.ineg(args[1]);
                return self.flatten_add(d, args[0], negb);
            }
            if name == p.neg && args.len() == 1 {
                return self.flatten_neg(d, args[0]);
            }
            if name == p.mul && args.len() == 2 {
                return self.flatten_mul(d, args[0], args[1]);
            }
        }
        let index = self.atom_index(e);
        let items = vec![Item::Mono(vec![index], false)];
        let proof = d.irefl(e);
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
        let source = d.iadd(u, v);
        let mid = d.iadd(fu, v);
        let joined = d.iadd(fu, fv);

        let step1 = d.icongr(u, fu, pu, &|d, t| d.iadd(t, v));
        let step2 = d.icongr(v, fv, pv, &|d, t| d.iadd(fu, t));
        let p12 = d.itrans(source, mid, joined, step1, step2);

        let mut items = iu.clone();
        items.extend_from_slice(&iv);
        let target = self.fold(d, &items);
        let step3 = self.reassoc(d, &iu, &iv);
        let proof = d.itrans(source, joined, target, p12, step3);
        Ok((items, proof))
    }

    /// `(items, proof : Eq Int (neg e) (fold items))` — distributes `neg`
    /// fully: `neg_add` over a sum, `mul_neg` over a product,
    /// [`Self::neg_neg_lemma`] over a double negation, and an opaque
    /// negated atom for anything else.
    fn flatten_neg(
        &mut self,
        d: &mut IntDev<'_>,
        e: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let neg_e = d.ineg(e);
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head) {
            if (name == p.ediv || name == p.emod) && !args.is_empty() {
                return Err(Decline::NonRing);
            }
            if name == p.neg && args.len() == 1 {
                let y = args[0];
                let (items, proof_y) = self.flatten(d, y)?;
                let nn = Self::neg_neg_lemma(d, y);
                let folded = self.fold(d, &items);
                let full = d.itrans(neg_e, y, folded, nn, proof_y);
                return Ok((items, full));
            }
            if name == p.add && args.len() == 2 {
                let (u, v) = (args[0], args[1]);
                let na = d.const_app(p.neg_add, &[u, v]);
                let neg_u = d.ineg(u);
                let neg_v = d.ineg(v);
                let add_negu_negv = d.iadd(neg_u, neg_v);
                let (items, proof_sum) = self.flatten_add(d, neg_u, neg_v)?;
                let folded = self.fold(d, &items);
                let full = d.itrans(neg_e, add_negu_negv, folded, na, proof_sum);
                return Ok((items, full));
            }
            if name == p.mul && args.len() == 2 {
                let (u, v) = (args[0], args[1]);
                let neg_v = d.ineg(v);
                let u_negv = d.imul(u, neg_v);
                let mn = d.const_app(p.mul_neg, &[u, v]);
                let rev = d.isymm(u_negv, neg_e, mn);
                let (items, proof_mul) = self.flatten_mul(d, u, neg_v)?;
                let folded = self.fold(d, &items);
                let full = d.itrans(neg_e, u_negv, folded, rev, proof_mul);
                return Ok((items, full));
            }
        }
        let idx = self.atom_index(e);
        let items = vec![Item::Mono(vec![idx], true)];
        let proof = d.irefl(neg_e);
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
        let source = d.imul(u, v);
        let mid = d.imul(fu, v);
        let joined = d.imul(fu, fv);

        let step1 = d.icongr(u, fu, pu, &|d, t| d.imul(t, v));
        let step2 = d.icongr(v, fv, pv, &|d, t| d.imul(fu, t));
        let p12 = d.itrans(source, mid, joined, step1, step2);

        let (dist_items, dist_proof) = self.distribute(d, &iu, &iv)?;
        let target = self.fold(d, &dist_items);
        let proof = d.itrans(source, joined, target, p12, dist_proof);
        Ok((dist_items, proof))
    }

    fn normalize(&mut self, d: &mut IntDev<'_>, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        let (items, p1) = self.flatten(d, e)?;
        let flat = self.fold(d, &items);
        let (sorted, p2) = self.sort_items(d, &items);
        let sorted_term = self.fold(d, &sorted);
        let (cancelled, p3) = self.cancel_pairs(d, &sorted);
        let cancelled_term = self.fold(d, &cancelled);
        let p12 = d.itrans(e, flat, sorted_term, p1, p2);
        let proof = d.itrans(e, sorted_term, cancelled_term, p12, p3);
        Ok((cancelled, proof))
    }

    /// `Eq Int (add zero a) a`, derived from `add_comm`/`add_zero` — the
    /// LEFT-zero law, not itself in `IntPrelude` (only the right-hand
    /// `add_zero` is).
    fn zero_add_lemma(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
        let p = d.int();
        let zero = d.izero();
        let za = d.iadd(zero, a);
        let az = d.iadd(a, zero);
        let comm = d.const_app(p.add_comm, &[zero, a]);
        let az_eq_a = d.const_app(p.add_zero, &[a]);
        d.itrans(za, az, a, comm, az_eq_a)
    }

    /// `Eq Int (fold_from d zero tail) (fold tail)`, `tail` nonempty — drops
    /// a leading `zero + …` from an additive fold.
    fn drop_leading_zero(&self, d: &mut IntDev<'_>, tail: &[Item]) -> ExprId {
        let t0 = self.item_term(d, &tail[0]);
        let za = Self::zero_add_lemma(d, t0);
        let zero = d.izero();
        let start = d.iadd(zero, t0);
        let rest = &tail[1..];
        d.icongr(start, t0, za, &|d, t| self.fold_from(d, t, rest))
    }

    /// One fixpoint pass cancelling adjacent `x` / `neg x` summands (same
    /// sorted factor list, opposite sign) via `add_neg`, `add_assoc` and
    /// `add_zero`/[`Self::zero_add_lemma`] — `sort_items` alone leaves
    /// `a + (-a) + a*a + (-1)` unsimplified, and `diff_of_squares`'s own
    /// target needs the cancellation (its hand proof's last step is exactly
    /// this, `int_prelude/modeq.rs::cancel_common_addend`). Sound and
    /// incomplete in the same spirit as `sort_factors`'s predecessor: only
    /// *adjacent*, *syntactically opposite-signed*, *same-monomial* pairs
    /// cancel — `x + y + (-x)` with something between does not.
    fn cancel_pairs(&mut self, d: &mut IntDev<'_>, items: &[Item]) -> (Vec<Item>, ExprId) {
        let source = self.fold(d, items);
        let mut current: Vec<Item> = items.to_vec();
        let mut proof = d.irefl(source);
        let mut folded = source;
        loop {
            let mut cancelled = false;
            let mut k = 0;
            while k + 1 < current.len() {
                let opposite = match (&current[k], &current[k + 1]) {
                    (Item::Mono(va, false), Item::Mono(vb, true)) => va == vb,
                    _ => false,
                };
                if !opposite {
                    k += 1;
                    continue;
                }
                let p = d.int();
                let x = self.item_term(d, &current[k]);
                let negx = self.item_term(d, &current[k + 1]);
                let an = d.const_app(p.add_neg, &[x]);
                let before_pair = d.iadd(x, negx);
                let zero = d.izero();
                let tail = current[k + 2..].to_vec();

                let (new_items, target, step) = if k == 0 {
                    if tail.is_empty() {
                        let new_items = vec![Item::Num(0)];
                        (new_items, zero, an)
                    } else {
                        let step1 =
                            d.icongr(before_pair, zero, an, &|d, t| self.fold_from(d, t, &tail));
                        let via_zero = self.fold_from(d, zero, &tail);
                        let target = self.fold(d, &tail);
                        let step2 = self.drop_leading_zero(d, &tail);
                        let chained = d.itrans(folded, via_zero, target, step1, step2);
                        (tail.clone(), target, chained)
                    }
                } else {
                    let prefix = current[..k].to_vec();
                    let fp = self.fold(d, &prefix);
                    let before_inner = d.iadd(fp, x);
                    let before = d.iadd(before_inner, negx);
                    let assoc = d.const_app(p.add_assoc, &[fp, x, negx]);
                    let fp_pair = d.iadd(fp, before_pair);
                    let congr_an = d.icongr(before_pair, zero, an, &|d, t| d.iadd(fp, t));
                    let fp_zero = d.iadd(fp, zero);
                    let az = d.const_app(p.add_zero, &[fp]);
                    let (_, base) =
                        d.ichain(before, &[(fp_pair, assoc), (fp_zero, congr_an), (fp, az)]);
                    let mut new_items = prefix.clone();
                    new_items.extend_from_slice(&tail);
                    let target = self.fold_from(d, fp, &tail);
                    let tail_step = d.icongr(before, fp, base, &|d, t| self.fold_from(d, t, &tail));
                    (new_items, target, tail_step)
                };

                proof = d.itrans(source, folded, target, proof, step);
                folded = target;
                current = new_items;
                cancelled = true;
                break;
            }
            if !cancelled {
                break;
            }
        }
        (current, proof)
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
        let back = d.isymm(y, canon_y, py);
        Ok(d.itrans(x, canon_x, y, px, back))
    }
}

/// Prove `Eq Int lhs rhs` from ring axioms alone, or decline.
///
/// # Errors
///
/// [`Decline`] whenever a side leaves the fragment or the two sides are not
/// (within this normalizer's completeness) the same ring expression.
pub(crate) fn prove_eq(
    d: &mut IntDev<'_>,
    prelude: &IntPrelude,
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
/// As [`prove_eq`], minus [`Decline::NotAnIdentity`]. An `Ok` here is
/// **not** a claim the term is well-typed.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn prove_eq_unverified(
    d: &mut IntDev<'_>,
    prelude: &IntPrelude,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(prelude);
    problem.prove_eq(d, lhs, rhs, false)
}

/// Prove `Eq (lhs args) (rhs args)` by proving the identity generically over
/// fresh variables and instantiating at `args` — `ring::nat::prove_eq_at`'s
/// exact contract, over `IntDev`.
///
/// # Errors
///
/// As [`prove_eq`], applied to the generic goal `build` states.
pub(crate) fn prove_eq_at(
    d: &mut IntDev<'_>,
    prelude: &IntPrelude,
    args: &[ExprId],
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
) -> Result<ExprId, Decline> {
    let int_ty = d.int_ty();
    let fvs: Vec<u64> = args.iter().map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (lhs, rhs) = build(d, &vars);
    let proof = prove_eq(d, prelude, lhs, rhs)?;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        value = d.lam_fv(fv, int_ty, value);
    }
    Ok(d.apply(value, args))
}

/// Prove `goal` (`Eq Int _ _`) from ring axioms alone, or decline.
///
/// # Errors
///
/// [`Decline::GoalNotAtomic`] when `goal`'s head is not `Eq` at `Int`;
/// otherwise as [`prove_eq`].
pub(crate) fn prove(
    d: &mut IntDev<'_>,
    prelude: &IntPrelude,
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(prelude);
    let (lhs, rhs) = problem.parse_eq_goal(d, goal)?;
    problem.prove_eq(d, lhs, rhs, true)
}

/// Why [`theorem`] produced no declaration.
#[derive(Debug)]
pub enum RingError {
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
    prelude: &IntPrelude,
    name: crate::NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> Result<ExprId, RingError> {
    let int_ty = d.int_ty();
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let concl = build(d, &vars);

    let proof = prove(d, prelude, concl).map_err(RingError::Declined)?;

    let mut ty = concl;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, int_ty, ty);
        value = d.lam_fv(fv, int_ty, value);
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
    prelude: &IntPrelude,
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
