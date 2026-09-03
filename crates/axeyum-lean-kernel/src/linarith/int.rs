//! The ℤ fragment: the same producer over the **constructed** integers.
//!
//! The search is shared with [`super::nat`] — a certificate is a certificate.
//! Everything else differs, and the differences are forced by the carrier:
//!
//! - **ℤ has no nonnegativity**, so the certificate's slack must be a
//!   *constant* `≥ 0`, not a linear form with nonnegative coefficients. A
//!   residual mentioning any atom is refused, where over ℕ it would be
//!   perfectly good slack.
//! - **Nothing reduces.** `Int.add` case-splits on **both** arguments, so
//!   `Int.add x c` at a symbolic `x` is stuck for every `c`. Where the ℕ
//!   normalizer got constant-merging and zero-dropping for free by ι-reduction,
//!   here every one of those steps is a lemma. The one place reduction still
//!   works is between two *closed* numerals, and the normalizer leans on it
//!   exactly there.
//! - **`Int.lt` is not `Int.le (a+1) b`.** It is its own definition by case
//!   analysis on the constructors (`int_prelude/defs.rs::declare_order_definitions`),
//!   so the ℕ trick of proving `Le (succ a) b` and letting δ close the gap does
//!   not transfer. Strictness moves through `lt_ofNat_add` and
//!   `lt_of_lt_of_le` instead.
//!
//! ## What this fragment does NOT do, precisely
//!
//! A `<` **hypothesis** keeps its strictness: `Int.le_succ_of_lt` gives
//! `le (a+1) b` directly (`lt_dest`'s witness `∃ i, b = a + ofNat (i+1)`
//! lifted through `add_le_add_left` on `Le (ofNat 1) (ofNat (i+1))`, via
//! `Int.lt.elim` rather than a hand-built `Exists.elim`). So
//! `a < b ⊢ a + 1 ≤ b` is now **proved**, not declined — this closed a
//! fragment edge ADR-1576 recorded as open. A `<` *goal* was already fine —
//! it goes out through `lt_ofNat_add`.
//!
//! `Int.neg` applied to a compound term is treated as an opaque atom rather
//! than distributed with `neg_add`. `neg` of an atom or a numeral is handled
//! exactly.
//!
//! **`Int.mul` is in this fragment only by a literal multiplier of magnitude
//! at most [`super::MAX_MULTIPLIER`]**, and that bound is load-bearing in a
//! way it is not on the ℕ side. Over ℕ, `Nat.mul x k` at a literal `k`
//! ι-reduces to the left-associated fold `((0 + x) + x) + …` for free.
//! `Int.mul` case-splits on both arguments, so `Int.mul x k` at a symbolic `x`
//! never ι-reduces regardless of `k` — the unrolling is a real lemma chain
//! (`left_distrib` + `mul_one`, one application per copy), so a literal
//! multiplier above the bound declines [`Decline::NonLinear`] rather than
//! growing the proof term, matching the certificate search's own reason for
//! [`super::MAX_MULTIPLIER`]. A product of two genuinely non-constant terms —
//! `Int.mul x y` for two atoms — is still not analysed at all: it is an
//! opaque atom on both the parsing and the normalizing side, consistently,
//! which is what matters: an inconsistency there would make the procedure
//! decline in confusing places rather than be unsound, but it would still be
//! a defect.

use crate::ExprNode;
use crate::IntPrelude;
use crate::NatOps;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;

use super::{
    Certificate, Coeff, Decline, LinForm, MAX_MULTIPLIER, find_certificate, find_refutation,
};

/// One summand of a canonical additive form over ℤ.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Item {
    /// `+ atomᵢ`.
    Pos(usize),
    /// `+ (neg atomᵢ)`.
    Neg(usize),
    /// A literal integer.
    Const(Coeff),
}

impl Item {
    /// The sort key. The constant comes **first** here, unlike over ℕ: nothing
    /// reduces on this carrier, so every rearrangement is a lemma, and putting
    /// the constant at the head means every *other* summand has a nonempty
    /// prefix. That in turn means every transposition is `add_right_comm` and
    /// every cancellation is `add_assoc`/`add_neg`/`add_zero` — no head cases
    /// at all, which is where the ℕ version's `add_comm` special case lived.
    ///
    /// `Pos` sorts before `Neg` of the same atom so a cancelling pair always
    /// ends up adjacent.
    fn key(self) -> usize {
        match self {
            Item::Const(_) => 0,
            Item::Pos(i) => (i + 1) * 2,
            Item::Neg(i) => (i + 1) * 2 + 1,
        }
    }
}

/// An atomic proposition of the fragment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    Le,
    Lt,
    Eq,
}

/// A hypothesis the procedure may use.
struct Hyp {
    lhs: ExprId,
    rhs: ExprId,
    form: LinForm,
    proof: ExprId,
}

/// The parsing/emission context for one ℤ goal.
pub(crate) struct Problem {
    prelude: IntPrelude,
    atoms: Vec<ExprId>,
}

impl Problem {
    pub(crate) fn new(prelude: &IntPrelude) -> Self {
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

    // --- parsing ------------------------------------------------------------

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

    /// `e` as a literal integer: `Int.zero`, `Int.one`, `Int.ofNat <numeral>`,
    /// `Int.negSucc <numeral>`, or `Int.neg` of any of those.
    fn int_numeral(&self, d: &mut IntDev<'_>, e: ExprId) -> Option<Coeff> {
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
            return self.int_numeral(d, args[0]).map(|k| -k);
        }
        None
    }

    /// Parse `e` into a linear form.
    fn parse_term(&mut self, d: &mut IntDev<'_>, e: ExprId) -> Result<LinForm, Decline> {
        if let Some(k) = self.int_numeral(d, e) {
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
            if name == p.sub && args.len() == 2 {
                // `Int.sub a b := add a (neg b)` — a plain definition, so this
                // is δβ and the emitted proof types at either spelling.
                let a = self.parse_term(d, args[0])?;
                let b = self.parse_term(d, args[1])?;
                let negated = b.checked_scale(-1).ok_or(Decline::SearchBudget)?;
                return a.checked_add(&negated).ok_or(Decline::SearchBudget);
            }
            if name == p.neg && args.len() == 1 {
                let inner = args[0];
                if self.is_simple(d, inner) {
                    let a = self.parse_term(d, inner)?;
                    return a.checked_scale(-1).ok_or(Decline::SearchBudget);
                }
                // `neg` of a compound: an opaque atom. Sound, and the module
                // docs say so.
                return Ok(LinForm::atom(self.atom_index(e)));
            }
            // A literal multiplier's own range check happens here; neither
            // factor being a literal falls through to the opaque atom below.
            if name == p.mul
                && args.len() == 2
                && let Some((base, k, _commuted)) = self.mul_literal(d, args[0], args[1])
            {
                if !(0..=MAX_MULTIPLIER).contains(&k) {
                    // A literal multiplier outside the unrollable range:
                    // decline rather than grow the proof term, matching
                    // the certificate search's own reason for the bound.
                    return Err(Decline::NonLinear);
                }
                let b = self.parse_term(d, base)?;
                return b.checked_scale(k).ok_or(Decline::SearchBudget);
            }
        }
        Ok(LinForm::atom(self.atom_index(e)))
    }

    /// If either operand of a `mul` is a literal integer, `Some((other, k,
    /// literal_was_on_the_left))`. `None` when neither side is a literal — the
    /// genuinely nonlinear case this fragment still abstracts to an atom.
    fn mul_literal(
        &self,
        d: &mut IntDev<'_>,
        u: ExprId,
        v: ExprId,
    ) -> Option<(ExprId, Coeff, bool)> {
        if let Some(k) = self.int_numeral(d, v) {
            return Some((u, k, false));
        }
        if let Some(k) = self.int_numeral(d, u) {
            return Some((v, k, true));
        }
        None
    }

    /// Whether `e` is an atom or a literal — the two shapes `neg` distributes
    /// over without needing `neg_add`.
    fn is_simple(&self, d: &mut IntDev<'_>, e: ExprId) -> bool {
        if self.int_numeral(d, e).is_some() {
            return true;
        }
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        match Self::head_const(d, head) {
            Some(name) => {
                !(args.len() == 2 && (name == p.add || name == p.sub || name == p.mul))
                    && !(args.len() == 1 && name == p.neg)
            }
            None => true,
        }
    }

    fn parse_prop(
        &mut self,
        d: &mut IntDev<'_>,
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
        if name == p.nat.logic.eq && args.len() == 3 {
            let int_ty = d.int_ty();
            if args[0] == int_ty {
                return Ok((Shape::Eq, args[1], args[2]));
            }
        }
        Err(Decline::GoalNotAtomic)
    }

    fn parse_not(&mut self, d: &mut IntDev<'_>, e: ExprId) -> Option<ExprId> {
        let not_ = self.prelude.nat.logic.not;
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head)
            && name == not_
            && args.len() == 1
        {
            return Some(args[0]);
        }
        None
    }

    // --- canonical forms ----------------------------------------------------

    /// The canonical item list: the constant first, then each atom repeated by
    /// `|coefficient|` as `Pos` or `Neg`.
    fn canon_items(form: &LinForm) -> Vec<Item> {
        let mut items = vec![Item::Const(form.const_term())];
        for (index, coeff) in form.atoms() {
            let item = if coeff > 0 {
                Item::Pos(index)
            } else {
                Item::Neg(index)
            };
            for _ in 0..coeff.abs() {
                items.push(item);
            }
        }
        items
    }

    /// The integer literal `k`, as `ofNat k` or `neg (ofNat |k|)`.
    fn literal(d: &mut IntDev<'_>, k: Coeff) -> ExprId {
        let magnitude = u32::try_from(k.abs()).unwrap_or(0);
        let nat = d.num(magnitude);
        let positive = d.of_nat(nat);
        if k < 0 { d.ineg(positive) } else { positive }
    }

    fn item_term(&self, d: &mut IntDev<'_>, item: Item) -> ExprId {
        match item {
            Item::Pos(i) => self.atoms[i],
            Item::Neg(i) => {
                let a = self.atoms[i];
                d.ineg(a)
            }
            Item::Const(k) => Self::literal(d, k),
        }
    }

    fn fold(&self, d: &mut IntDev<'_>, items: &[Item]) -> ExprId {
        let mut acc = self.item_term(d, items[0]);
        for &item in &items[1..] {
            let t = self.item_term(d, item);
            acc = d.iadd(acc, t);
        }
        acc
    }

    fn fold_from(&self, d: &mut IntDev<'_>, start: ExprId, items: &[Item]) -> ExprId {
        let mut acc = start;
        for &item in items {
            let t = self.item_term(d, item);
            acc = d.iadd(acc, t);
        }
        acc
    }

    fn canon_term(&self, d: &mut IntDev<'_>, form: &LinForm) -> ExprId {
        let items = Self::canon_items(form);
        self.fold(d, &items)
    }

    // --- the normalizer -----------------------------------------------------

    /// `Eq ((a+b)+c) ((a+c)+b)`. This prelude has no `Int.add_right_comm`;
    /// `add_assoc` + `add_comm` + `add_assoc` is it.
    fn add_right_comm(&self, d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
        let p = self.prelude;
        let ab = d.iadd(a, b);
        let abc = d.iadd(ab, c);
        let bc = d.iadd(b, c);
        let a_bc = d.iadd(a, bc);
        let cb = d.iadd(c, b);
        let a_cb = d.iadd(a, cb);
        let ac = d.iadd(a, c);
        let acb = d.iadd(ac, b);

        let assoc = d.const_app(p.add_assoc, &[a, b, c]);
        let comm = d.const_app(p.add_comm, &[b, c]);
        let under = d.icongr(bc, cb, comm, &|d, t| d.iadd(a, t));
        let back = d.const_app(p.add_assoc, &[a, c, b]);
        let back = d.isymm(acb, a_cb, back);
        let first = d.itrans(abc, a_bc, a_cb, assoc, under);
        d.itrans(abc, a_cb, acb, first, back)
    }

    /// `(items, proof : Eq e (fold items))`.
    fn flatten(&mut self, d: &mut IntDev<'_>, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        if let Some(k) = self.int_numeral(d, e) {
            let items = vec![Item::Const(k)];
            let folded = self.fold(d, &items);
            return Ok((items, d.irefl(folded)));
        }
        let p = self.prelude;
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head) {
            if name == p.add && args.len() == 2 {
                return self.flatten_add(d, args[0], args[1]);
            }
            if name == p.sub && args.len() == 2 {
                // δβ: `sub a b` unfolds to `add a (neg b)`, so the proof built
                // for the unfolded spelling types at the folded one.
                let negated = d.ineg(args[1]);
                return self.flatten_add(d, args[0], negated);
            }
            if name == p.neg && args.len() == 1 && self.is_simple(d, args[0]) {
                let inner = args[0];
                if let Some(k) = self.int_numeral(d, inner) {
                    let items = vec![Item::Const(-k)];
                    let folded = self.fold(d, &items);
                    return Ok((items, d.irefl(folded)));
                }
                let index = self.atom_index(inner);
                let items = vec![Item::Neg(index)];
                return Ok((items, d.irefl(e)));
            }
            // Mirrors `parse_term`'s mul handling: a literal outside the
            // range declines, neither factor literal falls through to atom.
            if name == p.mul
                && args.len() == 2
                && let Some((base, k, commuted)) = self.mul_literal(d, args[0], args[1])
            {
                if !(0..=MAX_MULTIPLIER).contains(&k) {
                    return Err(Decline::NonLinear);
                }
                return self.flatten_mul_unrolled(d, base, k, commuted);
            }
        }
        let index = self.atom_index(e);
        Ok((vec![Item::Pos(index)], d.irefl(e)))
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

        let step1 = d.icongr(u, fu, pu, &|d, x| d.iadd(x, v));
        let step2 = d.icongr(v, fv, pv, &|d, x| d.iadd(fu, x));
        let p12 = d.itrans(source, mid, joined, step1, step2);

        let mut items = iu.clone();
        items.extend_from_slice(&iv);
        let target = self.fold(d, &items);
        let step3 = self.reassoc(d, &iu, &iv);
        let proof = d.itrans(source, joined, target, p12, step3);
        Ok((items, proof))
    }

    /// `Eq (mul base (ofNat (succ n))) (add (mul base (ofNat n)) base)` — the
    /// "`mul_succ`" step this prelude does not name directly. `Int.mul` does
    /// not ι-reduce at a literal multiplier (unlike `Nat.mul`), so this is a
    /// real lemma chain rather than a free unfold: `ofNat (succ n)` is
    /// definitionally `add (ofNat n) (ofNat 1)` (pure ι/δ on `Nat.add`'s
    /// right-recursion and `Int.add`'s `ofNat`/`ofNat` case, no lemma spent),
    /// then `left_distrib` splits the product over that sum and `mul_one`
    /// collapses the unit factor.
    fn mul_succ_step(&self, d: &mut IntDev<'_>, base: ExprId, n_nat: ExprId) -> ExprId {
        let p = self.prelude;
        let one_nat = d.num(1);
        let one_int = d.of_nat(one_nat);
        let n_int = d.of_nat(n_nat);
        let succ_n_nat = d.succ(n_nat);
        let succ_n_int = d.of_nat(succ_n_nat);
        let n_plus_one = d.iadd(n_int, one_int);

        let lhs0 = d.imul(base, succ_n_int);
        let rhs0 = d.imul(base, n_plus_one);
        let step0 = d.irefl(rhs0);

        let mul_base_n = d.imul(base, n_int);
        let mul_base_one = d.imul(base, one_int);
        let joined = d.iadd(mul_base_n, mul_base_one);
        let distrib = d.const_app(p.left_distrib, &[base, n_int, one_int]);

        let one_step = d.const_app(p.mul_one, &[base]);
        let target = d.iadd(mul_base_n, base);
        let cong = d.icongr(mul_base_one, base, one_step, &|d, x| d.iadd(mul_base_n, x));

        let step_a = d.itrans(lhs0, rhs0, joined, step0, distrib);
        d.itrans(lhs0, joined, target, step_a, cong)
    }

    /// `mul base (ofNat count)` unrolled into repeated addition, for a
    /// literal `count` bounded by [`MAX_MULTIPLIER`] — every copy costs a real
    /// lemma application ([`Self::mul_succ_step`]), unlike ℕ where the same
    /// unrolling is free by ι-reduction, which is why the bound matters here.
    /// `commuted` says the literal was on the left in the source term
    /// (`k * base` rather than `base * k`), needing one extra `mul_comm`.
    fn flatten_mul_unrolled(
        &mut self,
        d: &mut IntDev<'_>,
        base: ExprId,
        count: Coeff,
        commuted: bool,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let count_u32 = u32::try_from(count).map_err(|_| Decline::NonLinear)?;
        let (ib, pb) = self.flatten(d, base)?;
        let fb = self.fold(d, &ib);

        let zero_nat = d.num(0);
        let zero_int = d.of_nat(zero_nat);
        let mul_zero_term = d.imul(base, zero_int);
        let mut current_items: Vec<Item> = vec![Item::Const(0)];
        let mut current = self.fold(d, &current_items);
        let mul_zero_proof = d.const_app(self.prelude.mul_zero, &[base]);
        let bridge = d.irefl(current);
        let mut proof = d.itrans(mul_zero_term, zero_int, current, mul_zero_proof, bridge);

        for j in 0..count_u32 {
            let j_nat = d.num(j);
            let j_int = d.of_nat(j_nat);
            let mul_base_j = d.imul(base, j_int);
            let step_j = self.mul_succ_step(d, base, j_nat);
            let succ_j_nat = d.succ(j_nat);
            let succ_j_int = d.of_nat(succ_j_nat);
            let mul_base_succj = d.imul(base, succ_j_int);

            let joined2 = d.iadd(mul_base_j, base);
            let widen = d.icongr(mul_base_j, current, proof, &|d, x| d.iadd(x, base));
            let mid = d.iadd(current, base);
            let base_step = d.icongr(base, fb, pb, &|d, x| d.iadd(current, x));
            let mid2 = d.iadd(current, fb);
            let p1 = d.itrans(joined2, mid, mid2, widen, base_step);

            let reassoc_pf = self.reassoc(d, &current_items, &ib);
            let mut next_items = current_items.clone();
            next_items.extend_from_slice(&ib);
            let next = self.fold(d, &next_items);
            let p2 = d.itrans(joined2, mid2, next, p1, reassoc_pf);

            proof = d.itrans(mul_base_succj, joined2, next, step_j, p2);
            current = next;
            current_items = next_items;
        }

        if !commuted {
            return Ok((current_items, proof));
        }
        let p = self.prelude;
        let count_nat = d.num(count_u32);
        let count_int = d.of_nat(count_nat);
        let source = d.imul(count_int, base);
        let flipped = d.imul(base, count_int);
        let comm = d.const_app(p.mul_comm, &[count_int, base]);
        let full = d.itrans(source, flipped, current, comm, proof);
        Ok((current_items, full))
    }

    /// `Eq (add (fold left) (fold right)) (fold (left ++ right))`.
    fn reassoc(&self, d: &mut IntDev<'_>, left: &[Item], right: &[Item]) -> ExprId {
        let fl = self.fold(d, left);
        if right.len() == 1 {
            let joined = self.fold_from(d, fl, right);
            return d.irefl(joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold(d, init);
        let last_t = self.item_term(d, last[0]);
        let fr = d.iadd(fi, last_t);

        let source = d.iadd(fl, fr);
        let regrouped_inner = d.iadd(fl, fi);
        let regrouped = d.iadd(regrouped_inner, last_t);
        let assoc = d.const_app(self.prelude.add_assoc, &[fl, fi, last_t]);
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

    /// Put a `Const(0)` at the head when there is not already a constant there,
    /// so every later step has a nonempty prefix to work against.
    ///
    /// `Eq x (add zero x)` from `add_comm` + `add_zero`; this prelude has no
    /// `Int.zero_add`.
    fn prepend_zero(&self, d: &mut IntDev<'_>, items: &[Item]) -> (Vec<Item>, ExprId) {
        let p = self.prelude;
        let head = self.item_term(d, items[0]);
        let zero = d.izero();
        let zero_head = d.iadd(zero, head);
        let head_zero = d.iadd(head, zero);
        let comm = d.const_app(p.add_comm, &[zero, head]);
        let drop = d.const_app(p.add_zero, &[head]);
        let forward = d.itrans(zero_head, head_zero, head, comm, drop);
        let back = d.isymm(zero_head, head, forward);
        let tail = items[1..].to_vec();
        let proof = d.icongr(head, zero_head, back, &|d, t| self.fold_from(d, t, &tail));
        let mut out = vec![Item::Const(0)];
        out.extend_from_slice(items);
        (out, proof)
    }

    /// Sort into canonical order, merge the leading constants, and cancel every
    /// adjacent `x + (neg x)` pair.
    ///
    /// Returns `(items, proof : Eq (fold input) (fold items))`.
    fn arrange(&self, d: &mut IntDev<'_>, items: &[Item]) -> (Vec<Item>, ExprId) {
        let p = self.prelude;
        let source = self.fold(d, items);
        let mut current: Vec<Item> = items.to_vec();
        let mut folded = source;
        let mut proof = d.irefl(source);

        // 1. bubble sort; every transposition has a nonempty prefix because the
        //    constant sorts first and one is always present.
        loop {
            let mut swapped = false;
            for k in 0..current.len().saturating_sub(1) {
                if current[k].key() <= current[k + 1].key() {
                    continue;
                }
                debug_assert!(k > 0, "the leading constant keeps every swap off the head");
                let x = self.item_term(d, current[k]);
                let y = self.item_term(d, current[k + 1]);
                let prefix = self.fold(d, &current[..k]);
                let before_inner = d.iadd(prefix, x);
                let before = d.iadd(before_inner, y);
                let after_inner = d.iadd(prefix, y);
                let after = d.iadd(after_inner, x);
                let base = self.add_right_comm(d, prefix, x, y);
                let tail = current[k + 2..].to_vec();
                let step = d.icongr(before, after, base, &|d, t| self.fold_from(d, t, &tail));
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

        // 2. merge the leading constants. Two *closed* numerals is the one
        //    place `Int.add` still reduces, so the step is `Eq.refl`.
        while current.len() >= 2
            && let (Item::Const(a), Item::Const(b)) = (current[0], current[1])
        {
            let merged = Item::Const(a + b);
            let x = self.item_term(d, current[0]);
            let y = self.item_term(d, current[1]);
            let before = d.iadd(x, y);
            let after = self.item_term(d, merged);
            let base = d.irefl(after);
            let tail = current[2..].to_vec();
            let step = d.icongr(before, after, base, &|d, t| self.fold_from(d, t, &tail));
            current.remove(0);
            current[0] = merged;
            let next = self.fold(d, &current);
            proof = d.itrans(source, folded, next, proof, step);
            folded = next;
        }

        // 3. cancel adjacent `x + (neg x)`.
        loop {
            let mut hit = None;
            for k in 0..current.len().saturating_sub(1) {
                if let (Item::Pos(i), Item::Neg(j)) = (current[k], current[k + 1])
                    && i == j
                {
                    hit = Some(k);
                    break;
                }
            }
            let Some(k) = hit else { break };
            debug_assert!(
                k > 0,
                "the leading constant keeps every cancellation off the head"
            );
            let x = self.item_term(d, current[k]);
            let neg_x = self.item_term(d, current[k + 1]);
            let prefix = self.fold(d, &current[..k]);
            let before_inner = d.iadd(prefix, x);
            let before = d.iadd(before_inner, neg_x);
            let x_neg_x = d.iadd(x, neg_x);
            let mid = d.iadd(prefix, x_neg_x);
            let zero = d.izero();
            let near = d.iadd(prefix, zero);

            let assoc = d.const_app(p.add_assoc, &[prefix, x, neg_x]);
            let cancel = d.const_app(p.add_neg, &[x]);
            let under = d.icongr(x_neg_x, zero, cancel, &|d, t| d.iadd(prefix, t));
            let drop = d.const_app(p.add_zero, &[prefix]);
            let to_near = d.itrans(before, mid, near, assoc, under);
            let base = d.itrans(before, near, prefix, to_near, drop);

            let tail = current[k + 2..].to_vec();
            let step = d.icongr(before, prefix, base, &|d, t| self.fold_from(d, t, &tail));
            current.drain(k..=k + 1);
            let next = self.fold(d, &current);
            proof = d.itrans(source, folded, next, proof, step);
            folded = next;
        }

        (current, proof)
    }

    /// `(form, proof : Eq e (canon_term form))`.
    fn normalize(&mut self, d: &mut IntDev<'_>, e: ExprId) -> Result<(LinForm, ExprId), Decline> {
        let (items, p1) = self.flatten(d, e)?;
        let flat = self.fold(d, &items);
        let (items, p2) = if matches!(items[0], Item::Const(_)) {
            (items, d.irefl(flat))
        } else {
            self.prepend_zero(d, &items)
        };
        let seeded = self.fold(d, &items);
        let chained = d.itrans(e, flat, seeded, p1, p2);

        let (arranged, p3) = self.arrange(d, &items);
        let arranged_term = self.fold(d, &arranged);
        let proof = d.itrans(e, seeded, arranged_term, chained, p3);

        let mut form = LinForm::zero();
        for &item in &arranged {
            let piece = match item {
                Item::Pos(i) => LinForm::atom(i),
                Item::Neg(i) => LinForm::atom(i).checked_scale(-1).unwrap_or_default(),
                Item::Const(k) => LinForm::constant(k),
            };
            form = form.checked_add(&piece).ok_or(Decline::SearchBudget)?;
        }
        debug_assert_eq!(
            arranged,
            Self::canon_items(&form),
            "the arrangement did not reach the canonical list",
        );
        Ok((form, proof))
    }

    /// `Eq x y` when both sides have the same linear form.
    fn prove_eq(
        &mut self,
        d: &mut IntDev<'_>,
        x: ExprId,
        y: ExprId,
        verify: bool,
    ) -> Result<ExprId, Decline> {
        let (fx, px) = self.normalize(d, x)?;
        let (fy, py) = self.normalize(d, y)?;
        if verify && fx != fy {
            return Err(Decline::NoCertificate);
        }
        let canon_x = self.canon_term(d, &fx);
        let canon_y = self.canon_term(d, &fy);
        let back = d.isymm(y, canon_y, py);
        Ok(d.itrans(x, canon_x, y, px, back))
    }

    // --- emission -----------------------------------------------------------

    /// Add two `≤` facts side by side. `Int.add_le_add` is two-sided already.
    fn add_le_add(
        &self,
        d: &mut IntDev<'_>,
        left: (ExprId, ExprId, ExprId),
        right: (ExprId, ExprId, ExprId),
    ) -> (ExprId, ExprId, ExprId) {
        let p = self.prelude;
        let (a, b, h1) = left;
        let (c, e, h2) = right;
        let proof = d.const_app(p.add_le_add, &[a, b, c, e, h1, h2]);
        let ac = d.iadd(a, c);
        let be = d.iadd(b, e);
        (ac, be, proof)
    }

    fn le_rewrite_right(
        d: &mut IntDev<'_>,
        x: ExprId,
        y: ExprId,
        z: ExprId,
        h: ExprId,
        e: ExprId,
    ) -> ExprId {
        let motive = d.ieq_motive(y, &|d, t| d.ile(x, t));
        d.itransport(y, motive, h, z, e)
    }

    fn le_rewrite_left(
        d: &mut IntDev<'_>,
        y: ExprId,
        w: ExprId,
        z: ExprId,
        h: ExprId,
        e: ExprId,
    ) -> ExprId {
        let motive = d.ieq_motive(y, &|d, t| d.ile(t, w));
        d.itransport(y, motive, h, z, e)
    }

    fn combine(
        &self,
        d: &mut IntDev<'_>,
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
        let zero = d.izero();
        let refl = d.const_app(self.prelude.le_refl, &[zero]);
        (zero, zero, refl)
    }

    /// Emit `Le lhs rhs` from a certificate whose residual is a nonnegative
    /// constant.
    fn emit_le(
        &mut self,
        d: &mut IntDev<'_>,
        hyps: &[Hyp],
        lhs: ExprId,
        rhs: ExprId,
        cert: &Certificate,
        verify: bool,
    ) -> Result<ExprId, Decline> {
        let p = self.prelude;
        if !cert.residual.is_constant() || cert.residual.const_term() < 0 {
            // Over ℤ an atom in the slack proves nothing — there is no
            // nonnegativity to lean on.
            return Err(Decline::NoCertificate);
        }
        let slack_size =
            u32::try_from(cert.residual.const_term()).map_err(|_| Decline::SearchBudget)?;
        let (a_term, b_term, hsum) = self.combine(d, hyps, cert);
        let slack_nat = d.num(slack_size);
        let slack = d.of_nat(slack_nat);

        let la = d.iadd(lhs, a_term);
        let lb = d.iadd(lhs, b_term);
        let h1 = d.const_app(p.add_le_add_left, &[a_term, b_term, lhs, hsum]);
        let las = d.iadd(la, slack);
        let lbs = d.iadd(lb, slack);
        let h2 = d.const_app(p.add_le_add_right, &[la, lb, slack, h1]);

        let ra = d.iadd(rhs, a_term);
        let identity = self.prove_eq(d, lbs, ra, verify)?;
        let h3 = Self::le_rewrite_right(d, las, lbs, ra, h2, identity);

        let ls = d.iadd(lhs, slack);
        let lsa = d.iadd(ls, a_term);
        let shuffle = self.add_right_comm(d, lhs, a_term, slack);
        let h4 = Self::le_rewrite_left(d, las, ra, lsa, h3, shuffle);

        // `add_le_add_iff_right : ∀ a b c, Iff (le (a+c) (b+c)) (le a b)`.
        let iff = d.const_app(p.add_le_add_iff_right, &[ls, rhs, a_term]);
        let inner_left = d.ile(lsa, ra);
        let inner_right = d.ile(ls, rhs);
        let mp = p.nat.logic.iff_mp;
        let h5 = d.const_app(mp, &[inner_left, inner_right, iff, h4]);

        let h6 = d.const_app(p.le_of_nat_add, &[lhs, slack_nat]);
        Ok(d.const_app(p.le_trans, &[lhs, ls, rhs, h6, h5]))
    }

    /// `Le (ofNat 1) (ofNat k)` for a literal `k ≥ 1`.
    ///
    /// `Int.le (ofNat m) (ofNat n)` δ-reduces to `Nat.le m n`, so the witness
    /// is `Nat.le.refl 1` followed by `k − 1` applications of `Nat.le.step`.
    fn one_le_literal(&self, d: &mut IntDev<'_>, k: u32) -> ExprId {
        let nat = self.prelude.nat;
        let one = d.num(1);
        let mut proof = d.const_app(nat.le_refl, &[one]);
        for j in 1..k {
            let upper = d.num(j);
            proof = d.const_app(nat.le_step, &[one, upper, proof]);
        }
        proof
    }
}

/// A hypothesis offered to the procedure: its type and a proof of it.
pub(crate) type Assumption = (ExprId, ExprId);

impl Problem {
    fn collect(&mut self, d: &mut IntDev<'_>, assumptions: &[Assumption]) -> Vec<Hyp> {
        let p = self.prelude;
        let mut out = Vec::new();
        for &(ty, proof) in assumptions {
            let Ok((shape, lhs, rhs)) = self.parse_prop(d, ty) else {
                continue;
            };
            match shape {
                Shape::Le | Shape::Lt => {
                    // A `<` hypothesis keeps its strictness: `Int.le_succ_of_lt`
                    // gives `le (a+1) b` directly, not merely `le a b`
                    // (`le_of_lt`). See the module docs for the fragment edge
                    // this closed, and `super::MAX_MULTIPLIER`'s sibling test
                    // for the case it does not (a strict goal, not hypothesis).
                    let (left, le_proof) = if shape == Shape::Lt {
                        let one_nat = d.num(1);
                        let one_int = d.of_nat(one_nat);
                        let shifted = d.iadd(lhs, one_int);
                        let strict = d.const_app(p.le_succ_of_lt, &[lhs, rhs, proof]);
                        (shifted, strict)
                    } else {
                        (lhs, proof)
                    };
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
                        proof: le_proof,
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
                    let refl_a = d.const_app(p.le_refl, &[lhs]);
                    let motive_up = d.ieq_motive(lhs, &|d, t| d.ile(lhs, t));
                    let forward = d.itransport(lhs, motive_up, refl_a, rhs, proof);
                    let refl_b = d.const_app(p.le_refl, &[lhs]);
                    let motive_down = d.ieq_motive(lhs, &|d, t| d.ile(t, lhs));
                    let backward = d.itransport(lhs, motive_down, refl_b, rhs, proof);
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

    fn prove_le(
        &mut self,
        d: &mut IntDev<'_>,
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

    fn prove_goal(
        &mut self,
        d: &mut IntDev<'_>,
        assumptions: &[Assumption],
        goal: ExprId,
    ) -> Result<ExprId, Decline> {
        let p = self.prelude;
        if let Some(inner) = self.parse_not(d, goal) {
            let fv = d.fresh_fvar();
            let h = d.kernel().fvar(fv);
            let mut enlarged = assumptions.to_vec();
            enlarged.push((inner, h));
            let hyps = self.collect(d, &enlarged);
            let forms: Vec<LinForm> = hyps.iter().map(|hyp| hyp.form.clone()).collect();
            let cert = find_refutation(&forms)?;
            let body = self.emit_false(d, &hyps, &cert)?;
            let int_ty = inner;
            return Ok(d.lam_fv(fv, int_ty, body));
        }

        let (shape, lhs, rhs) = self.parse_prop(d, goal)?;
        match shape {
            Shape::Le => {
                let hyps = self.collect(d, assumptions);
                self.prove_le(d, &hyps, lhs, rhs)
            }
            Shape::Lt => {
                // `Int.lt` is its own definition, not `le (a+1) b`. Route
                // through `lt_ofNat_add` and `lt_of_lt_of_le`.
                let hyps = self.collect(d, assumptions);
                let one_nat = d.num(1);
                let one_int = d.of_nat(one_nat);
                let shifted = d.iadd(lhs, one_int);
                let upper = self.prove_le(d, &hyps, shifted, rhs)?;
                let zero_nat = d.num(0);
                let strict = d.const_app(p.lt_of_nat_add, &[lhs, zero_nat]);
                Ok(d.const_app(p.lt_of_lt_of_le, &[lhs, shifted, rhs, strict, upper]))
            }
            Shape::Eq => {
                // Try the normalizer first: `a + (b + c) = b + (a + c)` needs no
                // order reasoning at all, and `le_antisymm` is declared late in
                // this prelude's build, so the direct route reaches call sites
                // the antisymmetry route cannot.
                if let Ok(direct) = self.prove_eq(d, lhs, rhs, true) {
                    return Ok(direct);
                }
                let hyps = self.collect(d, assumptions);
                let up = self.prove_le(d, &hyps, lhs, rhs)?;
                let down = self.prove_le(d, &hyps, rhs, lhs)?;
                Ok(d.const_app(p.le_antisymm, &[lhs, rhs, up, down]))
            }
        }
    }

    /// Emit `False` from a refutation certificate.
    fn emit_false(
        &mut self,
        d: &mut IntDev<'_>,
        hyps: &[Hyp],
        cert: &Certificate,
    ) -> Result<ExprId, Decline> {
        let p = self.prelude;
        if !cert.residual.is_constant() {
            return Err(Decline::NoCertificate);
        }
        let m = cert.residual.const_term();
        let m32 = u32::try_from(m).map_err(|_| Decline::SearchBudget)?;
        if m32 < 1 {
            return Err(Decline::NoCertificate);
        }
        let (a_term, b_term, hsum) = self.combine(d, hyps, cert);

        // `A = B + ofNat m` as linear forms, so `A ≤ B` reads `B + m ≤ B`.
        let m_nat = d.num(m32);
        let m_int = d.of_nat(m_nat);
        let shifted = d.iadd(b_term, m_int);
        let identity = self.prove_eq(d, a_term, shifted, true)?;
        let h1 = Self::le_rewrite_left(d, a_term, b_term, shifted, hsum, identity);

        // `B + 1 ≤ B + m` from `1 ≤ m` at literals.
        let one_nat = d.num(1);
        let one_int = d.of_nat(one_nat);
        let b_plus_one = d.iadd(b_term, one_int);
        let small = self.one_le_literal(d, m32);
        let h2 = d.const_app(p.add_le_add_left, &[one_int, m_int, b_term, small]);
        let h3 = d.const_app(p.le_trans, &[b_plus_one, shifted, b_term, h2, h1]);

        let zero_nat = d.num(0);
        let strict = d.const_app(p.lt_of_nat_add, &[b_term, zero_nat]);
        let lt_self = d.const_app(p.lt_of_lt_of_le, &[b_term, b_plus_one, b_term, strict, h3]);
        let irrefl = d.const_app(p.lt_irrefl, &[b_term]);
        Ok(d.apply(irrefl, &[lt_self]))
    }
}

/// Prove `goal` from `assumptions` over ℤ, or decline.
///
/// The returned term is **unchecked**; the kernel is what stands behind it.
pub(crate) fn prove(
    d: &mut IntDev<'_>,
    prelude: &IntPrelude,
    assumptions: &[Assumption],
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(prelude);
    problem.prove_goal(d, assumptions, goal)
}

/// Declare `theorem name : ∀ x₀ … x_{arity−1} : Int, hyp₀ → … → concl` with the
/// proof supplied by [`prove`].
///
/// # Errors
///
/// The kernel's rejection when the emitted term was refused, or
/// `UnknownConst { name }` when the search declined — see
/// [`super::nat::declare`] for why that is the exact report rather than an
/// approximate one.
pub(crate) fn declare(
    d: &mut IntDev<'_>,
    prelude: &IntPrelude,
    name: crate::NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (Vec<ExprId>, ExprId),
) -> Result<(), crate::KernelError> {
    let int_ty = d.int_ty();
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

    let Ok(proof) = prove(d, prelude, &assumptions, concl) else {
        return Err(crate::KernelError::UnknownConst { name });
    };

    let mut ty = concl;
    let mut value = proof;
    for (&hty, &hfv) in hyp_types.iter().zip(hyp_fvs.iter()).rev() {
        ty = d.arrow(hty, ty);
        value = d.lam_fv(hfv, hty, value);
    }
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, int_ty, ty);
        value = d.lam_fv(fv, int_ty, value);
    }
    d.declare_theorem(name, ty, value)
}

/// Emit the `≤` chain for a certificate the **caller** supplies.
///
/// `verify = false` skips the procedure's own arithmetic check so a corrupted
/// certificate reaches the kernel — the only way to ask whether the trust
/// anchor catches it. See [`super::nat::emit_le_from_certificate`].
#[cfg(test)]
pub(crate) fn emit_le_from_certificate(
    d: &mut IntDev<'_>,
    prelude: &IntPrelude,
    assumptions: &[Assumption],
    lhs: ExprId,
    rhs: ExprId,
    cert: &Certificate,
    verify: bool,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(prelude);
    let hyps = problem.collect(d, assumptions);
    let _ = problem.parse_term(d, lhs)?;
    let _ = problem.parse_term(d, rhs)?;
    problem.emit_le(d, &hyps, lhs, rhs, cert, verify)
}
