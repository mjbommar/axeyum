//! The ℕ fragment: parse `ExprId`s into linear constraints, search for a
//! Farkas certificate, and **emit a kernel proof term** for it.
//!
//! ## What the emitted term is made of
//!
//! Only lemmas that already exist in [`NatPrelude`](crate::NatPrelude). The
//! emitter never declares anything of its own, so it adds no trusted surface
//! and nothing it produces can be admitted except through
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration).
//!
//! | lemma | role |
//! | --- | --- |
//! | `Nat.le.refl` | the empty combination |
//! | `Nat.le_trans` | every chaining step |
//! | `Nat.le_add_right` | `L ≤ L + S` for the slack |
//! | `Nat.add_le_add_left` / `Nat.add_le_add_right` | scaling and combining hypotheses |
//! | `Nat.le_of_add_le_add_right` | cancelling the combined left-hand side |
//! | `Nat.le_succ_succ` | the refutation's successor step |
//! | `Nat.lt_irrefl` | the refutation's contradiction |
//! | `Nat.le_antisymm` | an `Eq` goal from two `≤` proofs |
//! | `Nat.add_comm` / `Nat.add_right_comm` / `Nat.add_assoc` | the normalizer |
//! | `Nat.mul_comm` | a numeral multiplier on the left |
//! | `Eq.refl` / `Eq.rec` (via `NatOps`) | congruence and transport |
//!
//! ## Why the whole emitter is additive
//!
//! A certificate multiplier `λ` is emitted as `λ` repeated additions, never as
//! `Nat.mul λ _` plus `mul_le_mul_left`. Two reasons, and the first is the one
//! that decides it: **every numeral in this kernel is unary**, so a `mul` route
//! puts the multiplier in a `Nat.mul` whose right operand must then be
//! distributed back out through `left_distrib`/`mul_assoc` — more lemmas, and
//! a term whose size grows the same way anyway. Second, `Nat.mul` recurses on
//! its **right** argument, so `mul λ x` at symbolic `x` is stuck and needs
//! `mul_comm` before anything reduces. Staying additive keeps every step
//! inside the four `add` lemmas above.
//!
//! `Nat.add` also recurses on its right argument, and the normalizer's
//! canonical form is built to exploit that: the constant is the **last**
//! summand, so `X + k` ι-reduces to `succ^k X` and every numeral bookkeeping
//! step — merging two trailing constants, dropping a trailing zero — is
//! definitional and costs no lemma at all.

use crate::ExprNode;
use crate::NatOps;
use crate::NatPrelude;
use crate::expr::ExprId;

use super::{Certificate, Coeff, Decline, LinForm, find_certificate, find_refutation};

/// One summand of a canonical additive form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Item {
    /// An index into the problem's atom table.
    Atom(usize),
    /// A literal `Nat` numeral.
    Num(Coeff),
}

impl Item {
    /// The sort key: atoms first in table order, every numeral last.
    fn key(self) -> usize {
        match self {
            Item::Atom(i) => i,
            Item::Num(_) => usize::MAX,
        }
    }
}

/// An atomic proposition of the fragment, as parsed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// `Nat.le a b`.
    Le,
    /// `Nat.lt a b`, i.e. `Nat.le (succ a) b`.
    Lt,
    /// `Eq Nat a b`.
    Eq,
}

/// A hypothesis the procedure may use: its assertion `lhs ≤ rhs` as terms, the
/// same assertion as a linear form (`rhs − lhs ≥ 0`), and a proof of it.
struct Hyp {
    lhs: ExprId,
    rhs: ExprId,
    form: LinForm,
    proof: ExprId,
}

/// The parsing/emission context for one goal.
pub struct Problem {
    prelude: NatPrelude,
    atoms: Vec<ExprId>,
}

impl Problem {
    /// A fresh problem over `prelude` with an empty atom table.
    #[must_use]
    pub fn new(prelude: NatPrelude) -> Self {
        Self {
            prelude,
            atoms: Vec::new(),
        }
    }

    /// The atoms discovered so far, in table order.
    #[must_use]
    pub fn atoms(&self) -> &[ExprId] {
        &self.atoms
    }

    fn atom_index(&mut self, e: ExprId) -> usize {
        if let Some(i) = self.atoms.iter().position(|&a| a == e) {
            return i;
        }
        self.atoms.push(e);
        self.atoms.len() - 1
    }

    // --- parsing ------------------------------------------------------------

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

    /// Parse `e` into a linear form, without building any proof.
    ///
    /// # Errors
    ///
    /// [`Decline::NonLinear`] when `e` contains a product of two non-constant
    /// subterms. Everything else — an opaque application, an `fvar`, a `sub` —
    /// becomes an atom, which is sound: an atom denotes some natural and the
    /// procedure learns nothing about it.
    pub fn parse_term<D: NatOps>(&mut self, d: &mut D, e: ExprId) -> Result<LinForm, Decline> {
        if let Some(k) = self.as_numeral(d, e) {
            return Ok(LinForm::constant(k));
        }
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head) {
            if name == p.add && args.len() == 2 {
                let a = self.parse_term(d, args[0])?;
                let b = self.parse_term(d, args[1])?;
                return a.checked_add(&b).ok_or(Decline::SearchBudget);
            }
            if name == p.succ && args.len() == 1 {
                let a = self.parse_term(d, args[0])?;
                return a
                    .checked_add(&LinForm::constant(1))
                    .ok_or(Decline::SearchBudget);
            }
            if name == p.mul && args.len() == 2 {
                let left = self.as_numeral(d, args[0]);
                let right = self.as_numeral(d, args[1]);
                return match (left, right) {
                    (Some(k), _) => {
                        let b = self.parse_term(d, args[1])?;
                        b.checked_scale(k).ok_or(Decline::SearchBudget)
                    }
                    (None, Some(k)) => {
                        let a = self.parse_term(d, args[0])?;
                        a.checked_scale(k).ok_or(Decline::SearchBudget)
                    }
                    (None, None) => Err(Decline::NonLinear),
                };
            }
        }
        Ok(LinForm::atom(self.atom_index(e)))
    }

    /// Parse a proposition into `(shape, lhs, rhs)`.
    ///
    /// # Errors
    ///
    /// [`Decline::GoalNotAtomic`] when the head is not `Nat.le`, `Nat.lt` or
    /// `Eq` at `Nat`.
    pub fn parse_prop<D: NatOps>(
        &mut self,
        d: &mut D,
        e: ExprId,
    ) -> Result<(Shape, ExprId, ExprId), Decline> {
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        let name = Self::head_const(d, head).ok_or(Decline::GoalNotAtomic)?;
        if name == p.le && args.len() == 2 {
            return Ok((Shape::Le, args[0], args[1]));
        }
        if name == p.lt && args.len() == 2 {
            return Ok((Shape::Lt, args[0], args[1]));
        }
        if name == p.logic.eq && args.len() == 3 {
            let nat = d.nat_ty();
            if args[0] == nat {
                return Ok((Shape::Eq, args[1], args[2]));
            }
        }
        Err(Decline::GoalNotAtomic)
    }

    /// `¬ P`, unpacked: `Not P` is `P → False`, so a `Pi` whose codomain is
    /// `False` and whose domain does not occur in it.
    fn parse_not<D: NatOps>(&mut self, d: &mut D, e: ExprId) -> Option<ExprId> {
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head)
            && name == p.logic.not
            && args.len() == 1
        {
            return Some(args[0]);
        }
        None
    }

    // --- canonical additive forms ------------------------------------------

    /// The canonical item list of a nonnegative form: each atom repeated by its
    /// coefficient in table order, then the constant as the final summand.
    fn canon_items(form: &LinForm) -> Option<Vec<Item>> {
        let mut items = Vec::new();
        for (index, coeff) in form.atoms() {
            if coeff < 0 {
                return None;
            }
            for _ in 0..coeff {
                items.push(Item::Atom(index));
            }
        }
        if form.const_term() < 0 {
            return None;
        }
        if form.const_term() > 0 || items.is_empty() {
            items.push(Item::Num(form.const_term()));
        }
        Some(items)
    }

    fn item_term<D: NatOps>(&self, d: &mut D, item: Item) -> ExprId {
        match item {
            Item::Atom(i) => self.atoms[i],
            Item::Num(k) => d.num(u32::try_from(k).unwrap_or(0)),
        }
    }

    /// The left-associated `add` fold of `items` (never called with an empty
    /// list — every item list carries at least one summand).
    fn fold<D: NatOps>(&self, d: &mut D, items: &[Item]) -> ExprId {
        let mut acc = self.item_term(d, items[0]);
        for &item in &items[1..] {
            let t = self.item_term(d, item);
            acc = d.add(acc, t);
        }
        acc
    }

    /// Fold `items` onto an existing accumulator.
    fn fold_from<D: NatOps>(&self, d: &mut D, start: ExprId, items: &[Item]) -> ExprId {
        let mut acc = start;
        for &item in items {
            let t = self.item_term(d, item);
            acc = d.add(acc, t);
        }
        acc
    }

    /// The canonical term of a nonnegative form.
    fn canon_term<D: NatOps>(&self, d: &mut D, form: &LinForm) -> Option<ExprId> {
        let items = Self::canon_items(form)?;
        Some(self.fold(d, &items))
    }

    // --- the normalizer -----------------------------------------------------

    /// `(items, proof : Eq e (fold items))`, flattening `e`'s additive
    /// structure in source order.
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
            if name == p.add && args.len() == 2 {
                return self.flatten_add(d, args[0], args[1]);
            }
            if name == p.succ && args.len() == 1 {
                // `succ u` is definitionally `add u 1` (Nat.add recurses on its
                // right argument), so the proof built for `add u 1` also types
                // at `succ u` and the kernel closes the gap by ι-reduction.
                let one = d.num(1);
                return self.flatten_add(d, args[0], one);
            }
            if name == p.mul && args.len() == 2 {
                return self.flatten_mul(d, args[0], args[1]);
            }
        }
        let index = self.atom_index(e);
        let items = vec![Item::Atom(index)];
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

    /// `Nat.mul` by a numeral, unrolled into repeated addition.
    ///
    /// `mul v (succ j) ≡ add (mul v j) v` and `mul v zero ≡ zero`, so
    /// `mul v k` at a **literal** `k` is *definitionally* the left-associated
    /// fold `((0 + v) + v) + …` with `k` copies. Nothing has to be proved about
    /// the unrolling itself. A numeral on the **left** is stuck (`Nat.mul`
    /// recurses on its right argument), so that case commutes first with
    /// `mul_comm`.
    fn flatten_mul<D: NatOps>(
        &mut self,
        d: &mut D,
        u: ExprId,
        v: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let (base, count, commuted) = match (self.as_numeral(d, u), self.as_numeral(d, v)) {
            (_, Some(k)) => (u, k, false),
            (Some(k), None) => (v, k, true),
            (None, None) => return Err(Decline::NonLinear),
        };
        self.flatten_mul_unrolled(d, base, count, commuted)
    }

    /// The unrolling of [`Self::flatten_mul`].
    ///
    /// `mul base k` is definitionally the fold `((0 + base) + base) + …`, so
    /// the only work is flattening each `base` copy — one `congr` per copy,
    /// chained left to right.
    fn flatten_mul_unrolled<D: NatOps>(
        &mut self,
        d: &mut D,
        base: ExprId,
        count: Coeff,
        commuted: bool,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let (ib, pb) = self.flatten(d, base)?;
        let fb = self.fold(d, &ib);

        // Rewrite the copies one at a time: each `congr` targets the outermost
        // `add`, so walk left to right building `Eq src current`.
        let zero = d.num(0);
        let mut current_items: Vec<Item> = vec![Item::Num(0)];
        let mut current = zero;
        let mut proof = d.refl(zero);
        let mut prefix = zero;
        for _ in 0..count {
            let src_next = d.add(prefix, base);
            // `Eq (add prefix base) (add current base)` from the running proof.
            let widen = d.congr(prefix, current, proof, &|d, x| d.add(x, base));
            let mid = d.add(current, base);
            // `Eq (add current base) (add current fb)` from `pb`.
            let held = current;
            let step = d.congr(base, fb, pb, &|d, x| d.add(held, x));
            let mid2 = d.add(current, fb);
            let p1 = d.trans(src_next, mid, mid2, widen, step);
            // `Eq (add current fb) (fold (current_items ++ ib))`.
            let reassoc = self.reassoc(d, &current_items, &ib);
            let mut next_items = current_items.clone();
            next_items.extend_from_slice(&ib);
            let next = self.fold(d, &next_items);
            proof = d.trans(src_next, mid2, next, p1, reassoc);
            prefix = src_next;
            current = next;
            current_items = next_items;
        }

        if !commuted {
            return Ok((current_items, proof));
        }
        // `mul k base` needs one `mul_comm` before the unrolling applies.
        let p = self.prelude;
        let num = d.num(u32::try_from(count).unwrap_or(0));
        let source = d.mul(num, base);
        let flipped = d.mul(base, num);
        let comm = d.lemma(p.mul_comm, &[num, base]);
        let full = d.trans(source, flipped, current, comm, proof);
        Ok((current_items, full))
    }

    /// `Eq (add (fold left) (fold right)) (fold (left ++ right))`.
    ///
    /// Pure re-association: `a + (b + c) = (a + b) + c`, applied from the right
    /// end of `right`.
    fn reassoc<D: NatOps>(&self, d: &mut D, left: &[Item], right: &[Item]) -> ExprId {
        let fl = self.fold(d, left);
        if right.len() == 1 {
            // `add (fold left) x` *is* `fold (left ++ [x])`.
            let joined = self.fold_from(d, fl, right);
            return d.refl(joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, last[0]);
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

    /// Sort `items` into canonical order, emitting one adjacent transposition
    /// per swap: `add_comm` at the head, `add_right_comm` anywhere else.
    ///
    /// Returns `(sorted, proof : Eq (fold items) (fold sorted))`.
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
                let x = self.item_term(d, current[k]);
                let y = self.item_term(d, current[k + 1]);
                let (inner_before, inner_after, base) = if k == 0 {
                    let before = d.add(x, y);
                    let after = d.add(y, x);
                    let lemma = d.lemma(self.prelude.add_comm, &[x, y]);
                    (before, after, lemma)
                } else {
                    let prefix = self.fold(d, &current[..k]);
                    let before_inner = d.add(prefix, x);
                    let before = d.add(before_inner, y);
                    let after_inner = d.add(prefix, y);
                    let after = d.add(after_inner, x);
                    let lemma = d.lemma(self.prelude.add_right_comm, &[prefix, x, y]);
                    (before, after, lemma)
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

    /// `(form, proof : Eq e (canon_term form))`.
    ///
    /// # Errors
    ///
    /// [`Decline::NonLinear`] from the parser.
    fn normalize<D: NatOps>(&mut self, d: &mut D, e: ExprId) -> Result<(LinForm, ExprId), Decline> {
        let (items, p1) = self.flatten(d, e)?;
        let flat = self.fold(d, &items);
        let (sorted, p2) = self.sort_items(d, &items);
        let sorted_term = self.fold(d, &sorted);
        let chained = d.trans(e, flat, sorted_term, p1, p2);

        let mut form = LinForm::zero();
        for &item in &sorted {
            let piece = match item {
                Item::Atom(i) => LinForm::atom(i),
                Item::Num(k) => LinForm::constant(k),
            };
            form = form.checked_add(&piece).ok_or(Decline::SearchBudget)?;
        }
        // The canonical term merges the trailing numerals and drops a trailing
        // zero. Both are ι-reductions of `Nat.add` on its right argument, so
        // the sorted term and the canonical term are definitionally equal and
        // the bridge is `Eq.refl`.
        let canon = self.canon_term(d, &form).ok_or(Decline::NonLinear)?;
        let bridge = d.refl(canon);
        let proof = d.trans(e, sorted_term, canon, chained, bridge);
        Ok((form, proof))
    }

    /// `Eq x y` whenever `x` and `y` have the same linear form.
    ///
    /// # Errors
    ///
    /// [`Decline::NonLinear`] when either side leaves the fragment;
    /// [`Decline::NoCertificate`] when the two forms differ (which is a
    /// procedure bug, not a user-facing outcome — every caller has already
    /// checked the identity arithmetically).
    fn prove_eq<D: NatOps>(
        &mut self,
        d: &mut D,
        x: ExprId,
        y: ExprId,
        verify: bool,
    ) -> Result<ExprId, Decline> {
        let (fx, px) = self.normalize(d, x)?;
        let (fy, py) = self.normalize(d, y)?;
        if verify && fx != fy {
            return Err(Decline::NoCertificate);
        }
        let canon_x = self.canon_term(d, &fx).ok_or(Decline::NonLinear)?;
        let canon_y = self.canon_term(d, &fy).ok_or(Decline::NonLinear)?;
        let back = d.symm(y, canon_y, py);
        // When the two forms disagree — which only happens on a certificate the
        // caller supplied and asked us not to check — this `trans` splices
        // `Eq canon_y y` into a slot typed `Eq canon_x y`, and the KERNEL is
        // what refuses it. That is the point: see the corrupted-certificate
        // tests.
        Ok(d.trans(x, canon_x, y, px, back))
    }

    // --- emission -----------------------------------------------------------

    /// Add two `≤` facts side by side.
    ///
    /// Each argument is a `(lhs, rhs, proof)` triple — the same shape
    /// [`Self::combine`] carries — and the result is the triple for
    /// `lhs₁ + lhs₂ ≤ rhs₁ + rhs₂`. This prelude has no two-sided
    /// `add_le_add`, so it is `add_le_add_right` then `add_le_add_left`
    /// through `le_trans`.
    fn add_le_add<D: NatOps>(
        &self,
        d: &mut D,
        left: (ExprId, ExprId, ExprId),
        right: (ExprId, ExprId, ExprId),
    ) -> (ExprId, ExprId, ExprId) {
        let p = self.prelude;
        let (a, b, h1) = left;
        let (c, e, h2) = right;
        let t1 = d.lemma(p.add_le_add_right, &[c, a, b, h1]);
        let t2 = d.lemma(p.add_le_add_left, &[b, c, e, h2]);
        let ac = d.add(a, c);
        let bc = d.add(b, c);
        let be = d.add(b, e);
        let proof = d.lemma(p.le_trans, &[ac, bc, be, t1, t2]);
        (ac, be, proof)
    }

    /// `h : Le x y`, `e : Eq y z ⊢ Le x z`.
    fn le_rewrite_right<D: NatOps>(
        d: &mut D,
        x: ExprId,
        y: ExprId,
        z: ExprId,
        h: ExprId,
        e: ExprId,
    ) -> ExprId {
        let motive = d.eq_motive(y, &|d, t| d.le(x, t));
        d.transport(y, motive, h, z, e)
    }

    /// `h : Le y w`, `e : Eq y z ⊢ Le z w`.
    fn le_rewrite_left<D: NatOps>(
        d: &mut D,
        y: ExprId,
        w: ExprId,
        z: ExprId,
        h: ExprId,
        e: ExprId,
    ) -> ExprId {
        let motive = d.eq_motive(y, &|d, t| d.le(t, w));
        d.transport(y, motive, h, z, e)
    }

    /// Build `(A, B, proof : Le A B)` for `Σⱼ λⱼ·(Aⱼ ≤ Bⱼ)`.
    ///
    /// The empty combination is `Le 0 0` by `Nat.le.refl`, which keeps the
    /// caller's arithmetic uniform: a goal needing no hypothesis still runs
    /// the same five steps.
    fn combine<D: NatOps>(
        &self,
        d: &mut D,
        hyps: &[Hyp],
        cert: &Certificate,
    ) -> (ExprId, ExprId, ExprId) {
        let mut acc: Option<(ExprId, ExprId, ExprId)> = None;
        for (index, multiplier) in cert.used() {
            let h = &hyps[index];
            let base = (h.lhs, h.rhs, h.proof);
            let mut scaled = base;
            for _ in 1..multiplier {
                scaled = self.add_le_add(d, scaled, base);
            }
            acc = Some(match acc {
                None => scaled,
                Some(running) => self.add_le_add(d, running, scaled),
            });
        }
        if let Some(triple) = acc {
            return triple;
        }
        let zero = d.num(0);
        let refl = d.const_app(self.prelude.le_refl, &[zero]);
        (zero, zero, refl)
    }

    /// Emit `Le lhs rhs` from a certificate.
    ///
    /// The chain, with `A`/`B` the combined hypothesis sides and `S` the
    /// certificate's slack:
    ///
    /// ```text
    ///   Hsum : A ≤ B
    ///   → L + A ≤ L + B                      (add_le_add_left)
    ///   → (L + A) + S ≤ (L + B) + S          (add_le_add_right)
    ///   → (L + A) + S ≤ R + A                (the normalizer's identity)
    ///   → (L + S) + A ≤ R + A                (add_right_comm)
    ///   → L + S ≤ R                          (le_of_add_le_add_right)
    ///   → L ≤ L + S ≤ R                      (le_add_right, le_trans)
    /// ```
    fn emit_le<D: NatOps>(
        &mut self,
        d: &mut D,
        hyps: &[Hyp],
        lhs: ExprId,
        rhs: ExprId,
        cert: &Certificate,
        verify: bool,
    ) -> Result<ExprId, Decline> {
        let p = self.prelude;
        let (a_term, b_term, hsum) = self.combine(d, hyps, cert);
        let slack = self
            .canon_term(d, &cert.residual)
            .ok_or(Decline::NoCertificate)?;

        let la = d.add(lhs, a_term);
        let lb = d.add(lhs, b_term);
        let h1 = d.lemma(p.add_le_add_left, &[lhs, a_term, b_term, hsum]);
        let las = d.add(la, slack);
        let lbs = d.add(lb, slack);
        let h2 = d.lemma(p.add_le_add_right, &[slack, la, lb, h1]);

        let ra = d.add(rhs, a_term);
        let identity = self.prove_eq(d, lbs, ra, verify)?;
        let h3 = Self::le_rewrite_right(d, las, lbs, ra, h2, identity);

        let ls = d.add(lhs, slack);
        let lsa = d.add(ls, a_term);
        let shuffle = d.lemma(p.add_right_comm, &[lhs, a_term, slack]);
        let h4 = Self::le_rewrite_left(d, las, ra, lsa, h3, shuffle);

        let h5 = d.lemma(p.le_of_add_le_add_right, &[a_term, ls, rhs, h4]);
        let h6 = d.lemma(p.le_add_right, &[lhs, slack]);
        Ok(d.lemma(p.le_trans, &[lhs, ls, rhs, h6, h5]))
    }

    /// Emit `False` from a refutation certificate.
    ///
    /// With `A`/`B` the combined sides, the certificate says
    /// `B_form − A_form = −m − N` for `m ≥ 1` and `N` in the nonnegative cone,
    /// i.e. `A = B + N + m` as linear forms. So `A ≤ B` reads
    /// `B + N + m ≤ B`, and `succ B ≤ B + N + m` closes it against
    /// `lt_irrefl`.
    fn emit_false<D: NatOps>(
        &mut self,
        d: &mut D,
        hyps: &[Hyp],
        cert: &Certificate,
    ) -> Result<ExprId, Decline> {
        let p = self.prelude;
        let m = cert.residual.const_term();
        if m < 1 {
            return Err(Decline::NoCertificate);
        }
        let mut leftover = cert.residual.clone();
        let leftover_constant = leftover.const_term();
        leftover = leftover
            .checked_sub(&LinForm::constant(leftover_constant))
            .ok_or(Decline::SearchBudget)?;

        let (a_term, b_term, hsum) = self.combine(d, hyps, cert);

        // `base = B + N`, then `A = base + m`.
        let base = if leftover == LinForm::zero() {
            b_term
        } else {
            let n_term = self
                .canon_term(d, &leftover)
                .ok_or(Decline::NoCertificate)?;
            d.add(b_term, n_term)
        };
        let m32 = u32::try_from(m).map_err(|_| Decline::SearchBudget)?;
        let m_num = d.num(m32);
        let base_plus_m = d.add(base, m_num);
        let identity = self.prove_eq(d, a_term, base_plus_m, true)?;
        let h1 = Self::le_rewrite_left(d, a_term, b_term, base_plus_m, hsum, identity);

        // `B ≤ base ≤ base + (m − 1)`.
        let pred_num = d.num(m32 - 1);
        let base_plus_pred = d.add(base, pred_num);
        let step_pred = d.lemma(p.le_add_right, &[base, pred_num]);
        let h2 = if base == b_term {
            step_pred
        } else {
            let leftover_term = self
                .canon_term(d, &leftover)
                .ok_or(Decline::NoCertificate)?;
            let to_base = d.lemma(p.le_add_right, &[b_term, leftover_term]);
            d.lemma(
                p.le_trans,
                &[b_term, base, base_plus_pred, to_base, step_pred],
            )
        };

        let succ_b = d.succ(b_term);
        let h3 = d.lemma(p.le_succ_succ, &[b_term, base_plus_pred, h2]);
        // `succ (base + (m − 1))` ι-reduces to `base + m`.
        let h4 = d.lemma(p.le_trans, &[succ_b, base_plus_m, b_term, h3, h1]);
        let irrefl = d.lemma(p.lt_irrefl, &[b_term]);
        Ok(d.apply(irrefl, &[h4]))
    }
}

/// A hypothesis offered to the procedure: its type and a proof of it.
pub type Assumption = (ExprId, ExprId);

/// Prove `goal` from `assumptions`, or decline.
///
/// The returned `ExprId` is an **unchecked** proof term. It is checked when the
/// caller pushes it through `Kernel::add_declaration` (or `Kernel::infer`), and
/// that is the only thing standing behind it — this function is search, not
/// trust.
///
/// # Errors
///
/// A [`Decline`] whenever the goal leaves the fragment or no certificate is
/// found within the search bounds. A decline is never a claim that the goal is
/// false.
pub fn prove<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    assumptions: &[Assumption],
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(*prelude);
    problem.prove_goal(d, assumptions, goal)
}

impl Problem {
    /// Collect the usable hypotheses: each becomes zero, one or two `≤` facts.
    fn collect<D: NatOps>(&mut self, d: &mut D, assumptions: &[Assumption]) -> Vec<Hyp> {
        let p = self.prelude;
        let mut out = Vec::new();
        for &(ty, proof) in assumptions {
            let Ok((shape, lhs, rhs)) = self.parse_prop(d, ty) else {
                continue;
            };
            match shape {
                Shape::Le | Shape::Lt => {
                    let left = if shape == Shape::Lt { d.succ(lhs) } else { lhs };
                    let (Ok(fl), Ok(fr)) = (self.parse_term(d, left), self.parse_term(d, rhs))
                    else {
                        continue;
                    };
                    let Some(form) = fr.checked_sub(&fl) else {
                        continue;
                    };
                    out.push(Hyp {
                        lhs: left,
                        rhs,
                        form,
                        proof,
                    });
                }
                Shape::Eq => {
                    let (Ok(fl), Ok(fr)) = (self.parse_term(d, lhs), self.parse_term(d, rhs))
                    else {
                        continue;
                    };
                    let (Some(up), Some(down)) = (fr.checked_sub(&fl), fl.checked_sub(&fr)) else {
                        continue;
                    };
                    let refl_l = d.const_app(p.le_refl, &[lhs]);
                    let motive_up = d.eq_motive(lhs, &|d, t| d.le(lhs, t));
                    let forward = d.transport(lhs, motive_up, refl_l, rhs, proof);
                    let refl_l2 = d.const_app(p.le_refl, &[lhs]);
                    let motive_down = d.eq_motive(lhs, &|d, t| d.le(t, lhs));
                    let backward = d.transport(lhs, motive_down, refl_l2, rhs, proof);
                    out.push(Hyp {
                        lhs,
                        rhs,
                        form: up,
                        proof: forward,
                    });
                    out.push(Hyp {
                        lhs: rhs,
                        rhs: lhs,
                        form: down,
                        proof: backward,
                    });
                }
            }
        }
        out
    }

    /// Prove one `≤` goal stated as terms.
    fn prove_le<D: NatOps>(
        &mut self,
        d: &mut D,
        hyps: &[Hyp],
        lhs: ExprId,
        rhs: ExprId,
    ) -> Result<ExprId, Decline> {
        let fl = self.parse_term(d, lhs)?;
        let fr = self.parse_term(d, rhs)?;
        let goal_form = fr.checked_sub(&fl).ok_or(Decline::SearchBudget)?;
        let forms: Vec<LinForm> = hyps.iter().map(|h| h.form.clone()).collect();
        let cert = find_certificate(&forms, &goal_form)?;
        self.emit_le(d, hyps, lhs, rhs, &cert, true)
    }

    fn prove_goal<D: NatOps>(
        &mut self,
        d: &mut D,
        assumptions: &[Assumption],
        goal: ExprId,
    ) -> Result<ExprId, Decline> {
        let p = self.prelude;
        if let Some(inner) = self.parse_not(d, goal) {
            // `¬ P`: assume `P` and refute the enlarged hypothesis set.
            let fv = d.fresh_fvar();
            let h = d.kernel().fvar(fv);
            let mut enlarged = assumptions.to_vec();
            enlarged.push((inner, h));
            let hyps = self.collect(d, &enlarged);
            let forms: Vec<LinForm> = hyps.iter().map(|hyp| hyp.form.clone()).collect();
            let cert = find_refutation(&forms)?;
            let body = self.emit_false(d, &hyps, &cert)?;
            return Ok(d.lam_fv(fv, inner, body));
        }

        let (shape, lhs, rhs) = self.parse_prop(d, goal)?;
        let hyps = self.collect(d, assumptions);
        match shape {
            Shape::Le => self.prove_le(d, &hyps, lhs, rhs),
            Shape::Lt => {
                // `Lt a b` δ-unfolds to `Le (succ a) b`.
                let succ_lhs = d.succ(lhs);
                self.prove_le(d, &hyps, succ_lhs, rhs)
            }
            Shape::Eq => {
                let up = self.prove_le(d, &hyps, lhs, rhs)?;
                let down = self.prove_le(d, &hyps, rhs, lhs)?;
                Ok(d.lemma(p.le_antisymm, &[lhs, rhs, up, down]))
            }
        }
    }
}

/// Declare `theorem name : ∀ x₀ … x_{arity−1}, hyp₀ → … → concl` with the
/// proof supplied by [`prove`].
///
/// `build` returns the hypothesis types and the conclusion; the proof term is
/// searched for and emitted, never written by hand. The kernel re-checks it
/// inside `add_declaration`, so an `Ok` here means the trusted gate accepted
/// the emitted term.
///
/// # Errors
///
/// [`LinarithError::Declined`] when the procedure found no term, or
/// [`LinarithError::Rejected`] when the kernel refused the one it found — the
/// second is a defect in the emitter and the tests treat it as one.
pub fn theorem<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    name: crate::NameId,
    arity: usize,
    build: &dyn Fn(&mut D, &[ExprId]) -> (Vec<ExprId>, ExprId),
) -> Result<ExprId, LinarithError> {
    let nat = d.nat_ty();
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (hyp_types, concl) = build(d, &vars);

    let hyp_fvs: Vec<u64> = hyp_types.iter().map(|_| d.fresh_fvar()).collect();
    let assumptions: Vec<Assumption> = hyp_types
        .iter()
        .zip(hyp_fvs.iter())
        .map(|(&ty, &fv)| {
            let h = d.kernel().fvar(fv);
            (ty, h)
        })
        .collect();

    let proof = prove(d, prelude, &assumptions, concl).map_err(LinarithError::Declined)?;

    let mut ty = concl;
    let mut value = proof;
    for (&hty, &hfv) in hyp_types.iter().zip(hyp_fvs.iter()).rev() {
        ty = d.arrow(hty, ty);
        value = d.lam_fv(hfv, hty, value);
    }
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, nat, ty);
        value = d.lam_fv(fv, nat, value);
    }
    d.declare_theorem(name, ty, value)
        .map_err(LinarithError::Rejected)?;
    Ok(ty)
}

/// Why [`theorem`] produced no declaration.
#[derive(Debug)]
pub enum LinarithError {
    /// The procedure found no certificate.
    Declined(Decline),
    /// The procedure emitted a term and the **kernel** refused it.
    Rejected(crate::KernelError),
}

impl core::fmt::Display for LinarithError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Declined(d) => write!(f, "linarith declined: {d:?}"),
            Self::Rejected(e) => write!(f, "kernel rejected the emitted term: {e:?}"),
        }
    }
}

/// The certificate the search finds for the `≤` goal `lhs ≤ rhs`, without
/// emitting anything.
///
/// Exposed so a caller can inspect — or deliberately corrupt — the certificate
/// before handing it back to [`emit_le_from_certificate`].
///
/// # Errors
///
/// As [`prove`].
pub fn certificate_for<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    assumptions: &[Assumption],
    lhs: ExprId,
    rhs: ExprId,
) -> Result<Certificate, Decline> {
    let mut problem = Problem::new(*prelude);
    let hyps = problem.collect(d, assumptions);
    let fl = problem.parse_term(d, lhs)?;
    let fr = problem.parse_term(d, rhs)?;
    let goal_form = fr.checked_sub(&fl).ok_or(Decline::SearchBudget)?;
    let forms: Vec<LinForm> = hyps.iter().map(|h| h.form.clone()).collect();
    find_certificate(&forms, &goal_form)
}

/// Emit the `≤` chain for a certificate the **caller** supplies.
///
/// `verify` decides who is allowed to catch a bad certificate. With `true` the
/// procedure checks the certificate's own identity arithmetically and declines
/// on a mismatch. With `false` it emits the term regardless — which is the only
/// way to ask the question that matters: *does the kernel reject a corrupted
/// certificate, or were we only ever caught by our own bookkeeping?* The
/// corrupted-certificate tests run with `false` and require a `KernelError`.
///
/// # Errors
///
/// As [`prove`]. With `verify = false` an `Ok` here is **not** a claim that the
/// term is well-typed — only `Kernel::infer` / `add_declaration` decides that.
pub fn emit_le_from_certificate<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    assumptions: &[Assumption],
    lhs: ExprId,
    rhs: ExprId,
    cert: &Certificate,
    verify: bool,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(*prelude);
    let hyps = problem.collect(d, assumptions);
    let _ = problem.parse_term(d, lhs)?;
    let _ = problem.parse_term(d, rhs)?;
    problem.emit_le(d, &hyps, lhs, rhs, cert, verify)
}

/// [`theorem`], with the outcome collapsed into the prelude build's own error
/// channel so a call site can use `?` alongside the hand-written declarations
/// around it.
///
/// A **decline** at a prelude call site is not a recoverable outcome: the goal
/// there is fixed source text, so a search that stops reaching it is a defect
/// in the producer. Reporting it as
/// [`KernelError::UnknownConst`](crate::KernelError::UnknownConst) is exact
/// rather than approximate — after a decline nothing declares `name`, and every
/// downstream reference to it fails on precisely that.
///
/// # Errors
///
/// The kernel's rejection when the emitted term was refused, or
/// `UnknownConst { name }` when the search declined and no term was built.
pub fn declare<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    name: crate::NameId,
    arity: usize,
    build: &dyn Fn(&mut D, &[ExprId]) -> (Vec<ExprId>, ExprId),
) -> Result<(), crate::KernelError> {
    match theorem(d, prelude, name, arity, build) {
        Ok(_) => Ok(()),
        Err(LinarithError::Rejected(e)) => Err(e),
        Err(LinarithError::Declined(_)) => Err(crate::KernelError::UnknownConst { name }),
    }
}
