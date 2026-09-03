//! The ℕ fragment: parse `ExprId`s into a canonical sum of monomials, and
//! **emit a kernel proof term** for `t₁ = t₂` when the two sides agree.
//!
//! ## What the emitted term is made of
//!
//! Only lemmas that already exist in [`NatPrelude`](crate::NatPrelude). This
//! producer never declares anything of its own, so it adds no trusted
//! surface and nothing it produces can be admitted except through
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration).
//!
//! | lemma | role |
//! | --- | --- |
//! | `Nat.add_assoc` / `Nat.add_comm` | the outer sum's normalizer — every adjacent transposition, head or not, is derived from these two on the spot, never from `Nat.add_right_comm` (see below) |
//! | `Nat.mul_assoc` | merging two monomials' factor lists |
//! | `Nat.mul_comm` | flipping a numeral coefficient from the left of a `mul` |
//! | `Nat.left_distrib` | distributing a single monomial over a sum |
//! | `Nat.right_distrib` | distributing a sum over a single monomial |
//! | `Eq.refl` / `Eq.rec` (via `NatOps`) | congruence, transport, and every `ι`-reduction bridge |
//!
//! `Nat.add_right_comm` is deliberately **not** in this table even though a
//! non-head swap is exactly its statement: `add_right_comm` is itself one of
//! this producer's own retirement targets, and at the moment its hand proof
//! is replaced by a call into this module, `Nat.add_right_comm` does not
//! exist in the kernel's environment yet. The swap is derived inline from
//! `add_assoc`/`add_comm` instead — see `Problem::sort_items`'s doc comment.
//!
//! ## Why a monomial's proof leans on raw `ι`-reduction, not lemmas
//!
//! `Nat.mul`/`Nat.add` both recurse on their **second** argument (see
//! `docs/contributor-guide/kernel-proof-engineering.md`). So `mul it
//! (numeral k)`, for *any* `it` (even a compound, symbolic monomial term),
//! `ι`-reduces all the way to the literal nested-`add` chain `(((0 + it) +
//! it) + … + it)` — the recursion is driven entirely by the numeral's own
//! `succ`-structure, never by `it`. That reduction is what lets
//! `Problem::scale_item` bridge with `d.refl` rather than a lemma. What it
//! is *not* enough for: `add zero it` for symbolic `it` is stuck (`Nat.add`
//! also recurses on its second argument, and `it` isn't a `succ`/`zero`
//! constructor), so the growing accumulator still needs an explicit
//! `reassoc` proof at every step, exactly as `linarith`'s ℕ fragment needs
//! for its own numeral unrolling.

use crate::ExprNode;
use crate::NatOps;
use crate::NatPrelude;
use crate::expr::ExprId;

use super::{Coeff, Decline, MAX_COEFF};

/// One summand of a canonical additive form: a monomial (a left-to-right
/// factor list, **not** re-sorted internally — see the module docs on
/// `x*y` vs `y*x`) or a literal numeral.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Item {
    /// Atom-table indices, in encounter order, one per factor (a repeated
    /// index is a power, e.g. `x*x` is `Mono([i, i])`).
    Mono(Vec<usize>),
    /// A literal `Nat` numeral.
    Num(Coeff),
}

impl Item {
    /// The sort key: every monomial before every numeral (numerals sort
    /// last, as `linarith`'s ℕ fragment does, so the trailing-constant
    /// convention keeps `+ k` on the far right); monomials compare by their
    /// factor-index list.
    fn key(&self) -> (bool, &[usize]) {
        match self {
            Item::Mono(v) => (false, v.as_slice()),
            Item::Num(_) => (true, &[]),
        }
    }
}

/// The parsing/emission context for one goal.
struct Problem {
    prelude: NatPrelude,
    atoms: Vec<ExprId>,
}

impl Problem {
    fn new(prelude: &NatPrelude) -> Self {
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

    /// Peel `f a₁ … aₙ` into its head and arguments.
    fn spine<D: NatOps>(d: &mut D, e: ExprId) -> (ExprId, Vec<ExprId>) {
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

    /// The constant name at the head of `e`, if any.
    fn head_const<D: NatOps>(d: &mut D, e: ExprId) -> Option<crate::NameId> {
        match d.kernel().expr_node(e).clone() {
            ExprNode::Const(n, _) => Some(n),
            _ => None,
        }
    }

    /// `e` as a closed numeral, if it is one.
    fn as_numeral<D: NatOps>(&self, d: &mut D, e: ExprId) -> Option<Coeff> {
        let mut current = e;
        let mut count: Coeff = 0;
        loop {
            match d.kernel().expr_node(current).clone() {
                ExprNode::Const(n, _) if n == self.prelude.zero => return Some(count),
                ExprNode::App(f, a) => match d.kernel().expr_node(f).clone() {
                    ExprNode::Const(n, _) if n == self.prelude.succ => {
                        count = count.checked_add(1)?;
                        current = a;
                    }
                    _ => return None,
                },
                _ => return None,
            }
        }
    }

    /// `Eq Nat lhs rhs`, unpacked.
    ///
    /// # Errors
    ///
    /// [`Decline::GoalNotAtomic`] when the head is not `Eq` at `Nat`.
    fn parse_eq_goal<D: NatOps>(
        &mut self,
        d: &mut D,
        e: ExprId,
    ) -> Result<(ExprId, ExprId), Decline> {
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        let name = Self::head_const(d, head).ok_or(Decline::GoalNotAtomic)?;
        if name == p.logic.eq && args.len() == 3 {
            let nat = d.nat_ty();
            if args[0] == nat {
                return Ok((args[1], args[2]));
            }
        }
        Err(Decline::GoalNotAtomic)
    }

    // --- item-list machinery (the outer sum) -----------------------------

    fn item_term<D: NatOps>(&self, d: &mut D, item: &Item) -> ExprId {
        match item {
            Item::Mono(vars) => self.fold_mul(d, vars),
            Item::Num(k) => d.num(u32::try_from(*k).unwrap_or(0)),
        }
    }

    /// The left-associated `add` fold of `items` (never called with an
    /// empty list).
    fn fold<D: NatOps>(&self, d: &mut D, items: &[Item]) -> ExprId {
        let mut acc = self.item_term(d, &items[0]);
        for item in &items[1..] {
            let t = self.item_term(d, item);
            acc = d.add(acc, t);
        }
        acc
    }

    fn fold_from<D: NatOps>(&self, d: &mut D, start: ExprId, items: &[Item]) -> ExprId {
        let mut acc = start;
        for item in items {
            let t = self.item_term(d, item);
            acc = d.add(acc, t);
        }
        acc
    }

    /// The left-associated `mul` fold of factor-table indices (never called
    /// with an empty list — a monomial always has at least one factor).
    fn fold_mul<D: NatOps>(&self, d: &mut D, vars: &[usize]) -> ExprId {
        let mut acc = self.atoms[vars[0]];
        for &v in &vars[1..] {
            let t = self.atoms[v];
            acc = d.mul(acc, t);
        }
        acc
    }

    /// `Eq (add (fold left) (fold right)) (fold (left ++ right))`.
    ///
    /// Pure re-association, identical in shape to `linarith::nat`'s helper
    /// of the same name — the item content differs, the associativity
    /// argument does not.
    fn reassoc<D: NatOps>(&self, d: &mut D, left: &[Item], right: &[Item]) -> ExprId {
        let fl = self.fold(d, left);
        if right.len() == 1 {
            let joined = self.fold_from(d, fl, right);
            return d.refl(joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, &last[0]);
        let fr = d.add(fi, last_t);

        let source = d.add(fl, fr);
        let regrouped_inner = d.add(fl, fi);
        let regrouped = d.add(regrouped_inner, last_t);
        let assoc = d.lemma(self.prelude.add_assoc, &[fl, fi, last_t]);
        let step1 = d.symm(regrouped, source, assoc);

        let inner = self.reassoc(d, left, init);
        let mut joined_items = left.to_vec();
        joined_items.extend_from_slice(init);
        let joined_inner = self.fold(d, &joined_items);
        let step2 = d.congr(regrouped_inner, joined_inner, inner, &|d, x| {
            d.add(x, last_t)
        });
        let target = d.add(joined_inner, last_t);
        d.trans(source, regrouped, target, step1, step2)
    }

    /// `Eq (mul (fold_mul left) (fold_mul right)) (fold_mul (left ++
    /// right))` — [`Self::reassoc`]'s multiplicative twin, over raw
    /// factor-index lists rather than `Item`s (a monomial's factor list has
    /// no numerals mixed in).
    fn reassoc_mul<D: NatOps>(&self, d: &mut D, left: &[usize], right: &[usize]) -> ExprId {
        let fl = self.fold_mul(d, left);
        if right.len() == 1 {
            let joined = d.mul(fl, self.atoms[right[0]]);
            return d.refl(joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold_mul(d, init);
        let last_t = self.atoms[last[0]];
        let fr = d.mul(fi, last_t);

        let source = d.mul(fl, fr);
        let regrouped_inner = d.mul(fl, fi);
        let regrouped = d.mul(regrouped_inner, last_t);
        let assoc = d.lemma(self.prelude.mul_assoc, &[fl, fi, last_t]);
        let step1 = d.symm(regrouped, source, assoc);

        let inner = self.reassoc_mul(d, left, init);
        let mut joined_vars = left.to_vec();
        joined_vars.extend_from_slice(init);
        let joined_inner = self.fold_mul(d, &joined_vars);
        let step2 = d.congr(regrouped_inner, joined_inner, inner, &|d, x| {
            d.mul(x, last_t)
        });
        let target = d.mul(joined_inner, last_t);
        d.trans(source, regrouped, target, step1, step2)
    }

    /// Sort a monomial's factor list into canonical (index) order, one
    /// adjacent transposition per swap — [`Self::sort_items`]'s exact
    /// pattern, ported from `+`/`add_assoc`/`add_comm` to `*`/`mul_assoc`/
    /// `mul_comm`. This is what makes `x*y = y*x` an identity: without it,
    /// two monomials built by multiplying the same factors in a different
    /// order compare as different item keys and the procedure declines
    /// (see `commuting_two_products_is_a_sized_negative`, now a positive
    /// test — see `commuting_two_products_is_now_an_identity`).
    fn sort_factors<D: NatOps>(&self, d: &mut D, vars: &[usize]) -> (Vec<usize>, ExprId) {
        let source = self.fold_mul(d, vars);
        let mut current: Vec<usize> = vars.to_vec();
        let mut proof = d.refl(source);
        let mut folded = source;
        loop {
            let mut swapped = false;
            for k in 0..current.len().saturating_sub(1) {
                if current[k] <= current[k + 1] {
                    continue;
                }
                let x = self.atoms[current[k]];
                let y = self.atoms[current[k + 1]];
                let (inner_before, inner_after, base) = if k == 0 {
                    let before = d.mul(x, y);
                    let after = d.mul(y, x);
                    let lemma = d.lemma(self.prelude.mul_comm, &[x, y]);
                    (before, after, lemma)
                } else {
                    let prefix = self.fold_mul(d, &current[..k]);
                    let before_inner = d.mul(prefix, x);
                    let before = d.mul(before_inner, y);
                    let xy = d.mul(x, y);
                    // (prefix*x)*y = prefix*(x*y)
                    let assoc1 = d.lemma(self.prelude.mul_assoc, &[prefix, x, y]);
                    let mid1 = d.mul(prefix, xy);
                    // prefix*(x*y) = prefix*(y*x)
                    let comm = d.lemma(self.prelude.mul_comm, &[x, y]);
                    let yx = d.mul(y, x);
                    let step2 = d.congr(xy, yx, comm, &|d, t| d.mul(prefix, t));
                    let mid2 = d.mul(prefix, yx);
                    // prefix*(y*x) = (prefix*y)*x
                    let after_inner = d.mul(prefix, y);
                    let after = d.mul(after_inner, x);
                    let assoc2 = d.lemma(self.prelude.mul_assoc, &[prefix, y, x]);
                    let step3 = d.symm(after, mid2, assoc2);
                    let (_, base) =
                        d.chain(before, &[(mid1, assoc1), (mid2, step2), (after, step3)]);
                    (before, after, base)
                };
                let tail = current[k + 2..].to_vec();
                let step = d.congr(inner_before, inner_after, base, &|d, t| {
                    self.fold_mul_from(d, t, &tail)
                });
                current.swap(k, k + 1);
                let next = self.fold_mul(d, &current);
                proof = d.trans(source, folded, next, proof, step);
                folded = next;
                swapped = true;
            }
            if !swapped {
                break;
            }
        }
        (current, proof)
    }

    /// [`Self::fold_mul`], starting the fold from an already-built `start`
    /// term instead of `vars[0]` — the multiplicative twin of
    /// [`Self::fold_from`], needed by [`Self::sort_factors`]'s tail congr.
    fn fold_mul_from<D: NatOps>(&self, d: &mut D, start: ExprId, vars: &[usize]) -> ExprId {
        let mut acc = start;
        for &v in vars {
            let t = self.atoms[v];
            acc = d.mul(acc, t);
        }
        acc
    }

    /// Sort `items` into canonical order, one adjacent transposition per
    /// swap. At the head this is `add_comm` directly; elsewhere it is
    /// **derived** from `add_assoc`/`add_comm` on the spot
    /// (`(P+x)+y = P+(x+y) = P+(y+x) = (P+y)+x`) rather than calling
    /// `Nat.add_right_comm` — deliberately: `add_right_comm` is itself one of
    /// this producer's own retirement targets
    /// (`nat_prelude/algebra.rs::declare_additive_theorems`), and at the
    /// point its hand proof is replaced by a call into this module, the name
    /// `Nat.add_right_comm` does not exist in the kernel's environment yet.
    /// A version of `sort_items` that called it would work in every test
    /// (which always runs against the *finished* prelude) and fail only at
    /// the one call site that matters, with `KernelError::UnknownConst` —
    /// this is the shape of bug `docs/contributor-guide/
    /// evidence-and-checker-discipline.md` warns a checker that always sees
    /// the finished artifact cannot catch.
    fn sort_items<D: NatOps>(&self, d: &mut D, items: &[Item]) -> (Vec<Item>, ExprId) {
        let source = self.fold(d, items);
        let mut current: Vec<Item> = items.to_vec();
        let mut proof = d.refl(source);
        let mut folded = source;
        loop {
            let mut swapped = false;
            for k in 0..current.len().saturating_sub(1) {
                if current[k].key() <= current[k + 1].key() {
                    continue;
                }
                let x = self.item_term(d, &current[k]);
                let y = self.item_term(d, &current[k + 1]);
                let (inner_before, inner_after, base) = if k == 0 {
                    let before = d.add(x, y);
                    let after = d.add(y, x);
                    let lemma = d.lemma(self.prelude.add_comm, &[x, y]);
                    (before, after, lemma)
                } else {
                    let prefix = self.fold(d, &current[..k]);
                    let before_inner = d.add(prefix, x);
                    let before = d.add(before_inner, y);
                    let xy = d.add(x, y);
                    // (prefix+x)+y = prefix+(x+y)
                    let assoc1 = d.lemma(self.prelude.add_assoc, &[prefix, x, y]);
                    let mid1 = d.add(prefix, xy);
                    // prefix+(x+y) = prefix+(y+x)
                    let comm = d.lemma(self.prelude.add_comm, &[x, y]);
                    let yx = d.add(y, x);
                    let step2 = d.congr(xy, yx, comm, &|d, t| d.add(prefix, t));
                    let mid2 = d.add(prefix, yx);
                    // prefix+(y+x) = (prefix+y)+x
                    let after_inner = d.add(prefix, y);
                    let after = d.add(after_inner, x);
                    let assoc2 = d.lemma(self.prelude.add_assoc, &[prefix, y, x]);
                    let step3 = d.symm(after, mid2, assoc2);
                    let (_, base) =
                        d.chain(before, &[(mid1, assoc1), (mid2, step2), (after, step3)]);
                    (before, after, base)
                };
                let tail = current[k + 2..].to_vec();
                let step = d.congr(inner_before, inner_after, base, &|d, t| {
                    self.fold_from(d, t, &tail)
                });
                current.swap(k, k + 1);
                let next = self.fold(d, &current);
                proof = d.trans(source, folded, next, proof, step);
                folded = next;
                swapped = true;
            }
            if !swapped {
                break;
            }
        }
        (current, proof)
    }

    // --- the multiplicative unroll (a numeral coefficient) --------------

    /// `Eq (mul (item_term item) (numeral count)) (fold [item; count])`, or
    /// — with `commuted` — `Eq (mul (numeral count) (item_term item)) (fold
    /// [item; count])` via one leading `mul_comm`.
    ///
    /// `count == 0` runs the loop zero times, giving `[Item::Num(0)]` with a
    /// `mul_zero`-shaped proof for free (the `commuted` bridge is still a
    /// real `mul_comm` application, since `mul (numeral 0) it` is stuck at
    /// symbolic `it` exactly as `mul it (numeral 0)` is not).
    fn scale_item<D: NatOps>(
        &mut self,
        d: &mut D,
        item: &Item,
        count: Coeff,
        commuted: bool,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        if !(0..=MAX_COEFF).contains(&count) {
            return Err(Decline::CoefficientTooLarge);
        }
        let it = self.item_term(d, item);
        let count_u = u32::try_from(count).unwrap_or(0);

        let zero = d.num(0);
        let mut current_items: Vec<Item> = vec![Item::Num(0)];
        let mut current = zero;
        let mut proof = d.refl(zero);
        let mut prefix = zero;
        for _ in 0..count_u {
            let src_next = d.add(prefix, it);
            let widen = d.congr(prefix, current, proof, &|d, x| d.add(x, it));
            let mid = d.add(current, it);
            let mut next_items = current_items.clone();
            next_items.push(item.clone());
            let next = self.fold(d, &next_items);
            let reassoc = self.reassoc(d, &current_items, std::slice::from_ref(item));
            proof = d.trans(src_next, mid, next, widen, reassoc);
            prefix = src_next;
            current = next;
            current_items = next_items;
        }
        // `prefix` is now literally the nested-`add` term `mul it (numeral
        // count)` reduces to — the bridge is `refl`, exactly the trick
        // `linarith::nat::flatten` uses for its own numeral base case.
        let count_num = d.num(count_u);
        let uncommuted_source = d.mul(it, count_num);
        let target = self.fold(d, &current_items);
        let bridge = d.refl(prefix);
        let base_proof = d.trans(uncommuted_source, prefix, target, bridge, proof);
        if !commuted {
            return Ok((current_items, base_proof));
        }
        let commuted_source = d.mul(count_num, it);
        let comm = d.lemma(self.prelude.mul_comm, &[count_num, it]);
        let full = d.trans(commuted_source, uncommuted_source, target, comm, base_proof);
        Ok((current_items, full))
    }

    /// `Eq (mul (item_term a) (item_term b)) (fold result)` for two single
    /// items — the base case the distribution recursion bottoms out at.
    fn combine_items<D: NatOps>(
        &mut self,
        d: &mut D,
        a: &Item,
        b: &Item,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        match (a, b) {
            (Item::Num(x), Item::Num(y)) => {
                let prod = x.checked_mul(*y).ok_or(Decline::CoefficientTooLarge)?;
                if prod.abs() > MAX_COEFF * MAX_COEFF {
                    return Err(Decline::CoefficientTooLarge);
                }
                let xa = d.num(u32::try_from(*x).unwrap_or(0));
                let yb = d.num(u32::try_from(*y).unwrap_or(0));
                let source = d.mul(xa, yb);
                let target = d.num(u32::try_from(prod).unwrap_or(0));
                // Two concrete numerals: `mul` recurses on its second
                // argument, which is concrete here, so this reduces fully.
                let proof = d.refl(target);
                let _ = source;
                Ok((vec![Item::Num(prod)], proof))
            }
            (Item::Num(k), Item::Mono(_)) => self.scale_item(d, b, *k, true),
            (Item::Mono(_), Item::Num(k)) => self.scale_item(d, a, *k, false),
            (Item::Mono(va), Item::Mono(vb)) => {
                let mut merged = va.clone();
                merged.extend_from_slice(vb);
                let ta = self.fold_mul(d, va);
                let tb = self.fold_mul(d, vb);
                let source = d.mul(ta, tb);
                let reassoc = self.reassoc_mul(d, va, vb);
                let merged_term = self.fold_mul(d, &merged);
                let (sorted, sort_proof) = self.sort_factors(d, &merged);
                let target_item = Item::Mono(sorted);
                let target = self.item_term(d, &target_item);
                let proof = d.trans(source, merged_term, target, reassoc, sort_proof);
                Ok((vec![target_item], proof))
            }
        }
    }

    /// `Eq (mul (item_term item) (fold iv)) (fold result)` — distributing
    /// one item over an already-flat right-hand item list, via
    /// `left_distrib` peeling one summand at a time.
    fn distribute_single<D: NatOps>(
        &mut self,
        d: &mut D,
        item: &Item,
        iv: &[Item],
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        if iv.len() == 1 {
            return self.combine_items(d, item, &iv[0]);
        }
        let (init, last) = iv.split_at(iv.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, &last[0]);
        let fv = d.add(fi, last_t);
        let it = self.item_term(d, item);
        let source = d.mul(it, fv);

        let mul_it_fi = d.mul(it, fi);
        let mul_it_last = d.mul(it, last_t);
        let sum = d.add(mul_it_fi, mul_it_last);
        let ld = d.lemma(self.prelude.left_distrib, &[it, fi, last_t]);

        let (items_init, proof_init) = self.distribute_single(d, item, init)?;
        let (items_last, proof_last) = self.combine_items(d, item, &last[0])?;
        let target_init = self.fold(d, &items_init);
        let target_last = self.fold(d, &items_last);
        let step_a = d.congr(mul_it_fi, target_init, proof_init, &|d, x| {
            d.add(x, mul_it_last)
        });
        let mid2 = d.add(target_init, mul_it_last);
        let step_b = d.congr(mul_it_last, target_last, proof_last, &|d, x| {
            d.add(target_init, x)
        });
        let mid3 = d.add(target_init, target_last);
        let step_ab = d.trans(sum, mid2, mid3, step_a, step_b);

        let mut items = items_init.clone();
        items.extend_from_slice(&items_last);
        let combined = self.fold(d, &items);
        let reassoc = self.reassoc(d, &items_init, &items_last);
        let joined_proof = d.trans(sum, mid3, combined, step_ab, reassoc);
        let full = d.trans(source, sum, combined, ld, joined_proof);
        Ok((items, full))
    }

    /// `Eq (mul (fold iu) (fold iv)) (fold result)` — distributing a whole
    /// flat left-hand item list over `iv`, via `right_distrib` peeling one
    /// summand at a time and [`Self::distribute_single`] per summand.
    fn distribute<D: NatOps>(
        &mut self,
        d: &mut D,
        iu: &[Item],
        iv: &[Item],
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        if iu.len() == 1 {
            return self.distribute_single(d, &iu[0], iv);
        }
        let (init, last) = iu.split_at(iu.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, &last[0]);
        let fu = d.add(fi, last_t);
        let fv = self.fold(d, iv);
        let source = d.mul(fu, fv);

        let mul_fi_fv = d.mul(fi, fv);
        let mul_last_fv = d.mul(last_t, fv);
        let sum = d.add(mul_fi_fv, mul_last_fv);
        let rd = d.lemma(self.prelude.right_distrib, &[fi, last_t, fv]);

        let (items_init, proof_init) = self.distribute(d, init, iv)?;
        let (items_last, proof_last) = self.distribute_single(d, &last[0], iv)?;
        let target_init = self.fold(d, &items_init);
        let target_last = self.fold(d, &items_last);
        let step_a = d.congr(mul_fi_fv, target_init, proof_init, &|d, x| {
            d.add(x, mul_last_fv)
        });
        let mid2 = d.add(target_init, mul_last_fv);
        let step_b = d.congr(mul_last_fv, target_last, proof_last, &|d, x| {
            d.add(target_init, x)
        });
        let mid3 = d.add(target_init, target_last);
        let step_ab = d.trans(sum, mid2, mid3, step_a, step_b);

        let mut items = items_init.clone();
        items.extend_from_slice(&items_last);
        let combined = self.fold(d, &items);
        let reassoc = self.reassoc(d, &items_init, &items_last);
        let joined_proof = d.trans(sum, mid3, combined, step_ab, reassoc);
        let full = d.trans(source, sum, combined, rd, joined_proof);
        Ok((items, full))
    }

    // --- flatten: source term -> raw item list ---------------------------

    /// `(items, proof : Eq e (fold items))`, flattening `e`'s additive and
    /// multiplicative structure in source order.
    ///
    /// # Errors
    ///
    /// [`Decline::NonRing`] for `div`/`mod`/`sub` (ℕ's truncated
    /// subtraction is not a ring operation); [`Decline::CoefficientTooLarge`]
    /// from the multiplicative unroll.
    fn flatten<D: NatOps>(&mut self, d: &mut D, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        if let Some(k) = self.as_numeral(d, e) {
            let items = vec![Item::Num(k)];
            let folded = self.fold(d, &items);
            let proof = d.refl(folded);
            return Ok((items, proof));
        }
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head) {
            if (name == p.div || name == p.mod_ || name == p.sub) && !args.is_empty() {
                return Err(Decline::NonRing);
            }
            if name == p.add && args.len() == 2 {
                return self.flatten_add(d, args[0], args[1]);
            }
            if name == p.succ && args.len() == 1 {
                let one = d.num(1);
                return self.flatten_add(d, args[0], one);
            }
            if name == p.mul && args.len() == 2 {
                return self.flatten_mul(d, args[0], args[1]);
            }
        }
        let index = self.atom_index(e);
        let items = vec![Item::Mono(vec![index])];
        let proof = d.refl(e);
        Ok((items, proof))
    }

    fn flatten_add<D: NatOps>(
        &mut self,
        d: &mut D,
        u: ExprId,
        v: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let (iu, pu) = self.flatten(d, u)?;
        let (iv, pv) = self.flatten(d, v)?;
        let fu = self.fold(d, &iu);
        let fv = self.fold(d, &iv);
        let source = d.add(u, v);
        let mid = d.add(fu, v);
        let joined = d.add(fu, fv);

        let step1 = d.congr(u, fu, pu, &|d, x| d.add(x, v));
        let step2 = d.congr(v, fv, pv, &|d, x| d.add(fu, x));
        let p12 = d.trans(source, mid, joined, step1, step2);

        let mut items = iu.clone();
        items.extend_from_slice(&iv);
        let target = self.fold(d, &items);
        let step3 = self.reassoc(d, &iu, &iv);
        let proof = d.trans(source, joined, target, p12, step3);
        Ok((items, proof))
    }

    fn flatten_mul<D: NatOps>(
        &mut self,
        d: &mut D,
        u: ExprId,
        v: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let (iu, pu) = self.flatten(d, u)?;
        let (iv, pv) = self.flatten(d, v)?;
        let fu = self.fold(d, &iu);
        let fv = self.fold(d, &iv);
        let source = d.mul(u, v);
        let mid = d.mul(fu, v);
        let joined = d.mul(fu, fv);

        let step1 = d.congr(u, fu, pu, &|d, x| d.mul(x, v));
        let step2 = d.congr(v, fv, pv, &|d, x| d.mul(fu, x));
        let p12 = d.trans(source, mid, joined, step1, step2);

        let (dist_items, dist_proof) = self.distribute(d, &iu, &iv)?;
        let target = self.fold(d, &dist_items);
        let proof = d.trans(source, joined, target, p12, dist_proof);
        Ok((dist_items, proof))
    }

    /// `(sorted_items, proof : Eq e (fold sorted_items))`.
    fn normalize<D: NatOps>(
        &mut self,
        d: &mut D,
        e: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let (items, p1) = self.flatten(d, e)?;
        let flat = self.fold(d, &items);
        let (sorted, p2) = self.sort_items(d, &items);
        let sorted_term = self.fold(d, &sorted);
        let proof = d.trans(e, flat, sorted_term, p1, p2);
        Ok((sorted, proof))
    }

    /// `Eq x y` whenever `x` and `y` normalize to the same item list.
    ///
    /// # Errors
    ///
    /// As [`Self::normalize`]; [`Decline::NotAnIdentity`] when the two
    /// normal forms differ **and** `verify` is set — with `verify = false`
    /// this still builds and returns a term (see the module-level
    /// corrupted-certificate framing `linarith` established), and it is the
    /// *kernel*, not this check, that is supposed to refuse it.
    fn prove_eq<D: NatOps>(
        &mut self,
        d: &mut D,
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
        let back = d.symm(y, canon_y, py);
        // When the two normal forms disagree — only reachable with
        // `verify = false`, i.e. only from the corrupted-certificate tests —
        // this splices an `Eq canon_y y`-shaped proof into a slot typed `Eq
        // canon_x y`, and the KERNEL is what refuses it.
        Ok(d.trans(x, canon_x, y, px, back))
    }
}

/// Prove `Eq Nat lhs rhs` from ring axioms alone, or decline.
///
/// The returned `ExprId` is an **unchecked** proof term; the caller pushes
/// it through `Kernel::add_declaration` / `Kernel::infer`, exactly as with
/// `linarith::nat::prove`.
///
/// # Errors
///
/// [`Decline`] whenever a side leaves the fragment or the two sides are not
/// (within this normalizer's completeness) the same ring expression.
pub fn prove_eq<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(prelude);
    problem.prove_eq(d, lhs, rhs, true)
}

/// [`prove_eq`] with the procedure's own normal-form check switched off —
/// exposed only so the corrupted-certificate tests can ask "does the KERNEL
/// refuse this, or only our own bookkeeping?" ([`Decline::NotAnIdentity`] is
/// otherwise unreachable from this entry point).
///
/// # Errors
///
/// As [`prove_eq`], minus [`Decline::NotAnIdentity`]. An `Ok` here is
/// **not** a claim the term is well-typed.
pub fn prove_eq_unverified<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(prelude);
    problem.prove_eq(d, lhs, rhs, false)
}

/// Prove `Eq lhs(args) rhs(args)` by proving the identity **generically**
/// over fresh variables and instantiating the result at `args` via ordinary
/// application, rather than normalizing `lhs`/`rhs` themselves.
///
/// This is the right entry point whenever the two sides are built from
/// caller-supplied `args` that may themselves be outside the ring fragment
/// (a `div`/`mod` subterm, say) — `build` receives fresh free variables, so
/// the normalizer never sees `args`' actual structure, only their `Nat`
/// type. The generic proof is then wrapped in `arity` lambdas and applied to
/// `args`; the kernel's ordinary Pi-application typing does the rest,
/// regardless of what `args` are built from.
///
/// Found the hard way: `nat_prelude/div_mod_lemmas.rs`'s private
/// `add_add_add_comm(d, p, a, b, c, dd)` helper is called with `a`/`b`/`c`
/// built from `Nat.div`/`Nat.mod` — [`prove_eq`] on the literal substituted
/// terms declines `NonRing`, correctly (those terms really do leave the
/// fragment), even though the identity holds for **any** four naturals.
/// This function is how a producer stays sound about the substituted terms
/// while still discharging the caller's actual goal.
///
/// # Errors
///
/// As [`prove_eq`], applied to the **generic** (fresh-variable) goal
/// `build` states — never to `args` themselves.
pub fn prove_eq_at<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    args: &[ExprId],
    build: &dyn Fn(&mut D, &[ExprId]) -> (ExprId, ExprId),
) -> Result<ExprId, Decline> {
    let nat = d.nat_ty();
    let fvs: Vec<u64> = args.iter().map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (lhs, rhs) = build(d, &vars);
    let proof = prove_eq(d, prelude, lhs, rhs)?;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        value = d.lam_fv(fv, nat, value);
    }
    Ok(d.apply(value, args))
}

/// Prove `goal` (`Eq Nat _ _`) from ring axioms alone, or decline.
///
/// # Errors
///
/// [`Decline::GoalNotAtomic`] when `goal`'s head is not `Eq` at `Nat`;
/// otherwise as [`prove_eq`].
pub fn prove<D: NatOps>(d: &mut D, prelude: &NatPrelude, goal: ExprId) -> Result<ExprId, Decline> {
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
pub fn theorem<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    name: crate::NameId,
    arity: usize,
    build: &dyn Fn(&mut D, &[ExprId]) -> ExprId,
) -> Result<ExprId, RingError> {
    let nat = d.nat_ty();
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let concl = build(d, &vars);

    let proof = prove(d, prelude, concl).map_err(RingError::Declined)?;

    let mut ty = concl;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, nat, ty);
        value = d.lam_fv(fv, nat, value);
    }
    d.declare_theorem(name, ty, value)
        .map_err(RingError::Rejected)?;
    Ok(ty)
}

/// [`theorem`], with the outcome collapsed into the prelude build's own
/// error channel so a call site can use `?` alongside the hand-written
/// declarations around it.
///
/// # Errors
///
/// The kernel's rejection when the emitted term was refused, or
/// `UnknownConst { name }` when the search declined and no term was built —
/// see `linarith::nat::declare`'s docs for why that mapping is exact rather
/// than approximate.
pub fn declare<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    name: crate::NameId,
    arity: usize,
    build: &dyn Fn(&mut D, &[ExprId]) -> ExprId,
) -> Result<(), crate::KernelError> {
    match theorem(d, prelude, name, arity, build) {
        Ok(_) => Ok(()),
        Err(RingError::Rejected(e)) => Err(e),
        Err(RingError::Declined(_)) => Err(crate::KernelError::UnknownConst { name }),
    }
}
