//! Concrete-instance tests for `nat_prelude::subset_search` and
//! `nat_prelude::strong_induction`.
//!
//! The trusted gate cannot tell you a `Definition` is wrong — `bitB`,
//! `decode`, `encodeFrom`, `encode` and `anySubset` are admitted on their TYPE,
//! and a decoder that read the bits in the other order has exactly the same
//! type. So each is reduced here at tiny arguments and paired with the wrong
//! formula it rules out:
//!
//! * a `bitB` comparing against `0` instead of `1` would invert every answer;
//! * a `decode` that did not inherit `memB`'s truncation would report a member
//!   at or above the width, and `card (decode 2 7)` would be `3`, not `2`;
//! * an `encodeFrom` that walked the start index DOWNWARD, or wrote the bits in
//!   the reverse order, would send `{0}` and `{1}` to each other's codes;
//! * an `anySubset` that dropped one of its two negations would be the
//!   universal quantifier over subsets rather than the existential.
//!
//! Every theorem is offered to the trusted gate twice: once at its real
//! statement (must be ADMITTED) and once at a statement slid by one small term
//! (must be REJECTED). All widths stay at `n ≤ 3`, because every `Nat` numeral
//! in this prelude is unary and the search range is `pow 2 n`.

use crate::expr::ExprId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
    counter: u32,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self {
            k,
            p,
            st,
            counter: 0,
        }
    }

    /// A fresh scratch name for an accept/reject control.
    fn scratch(&mut self) -> crate::NameId {
        self.counter += 1;
        let anon = self.k.anon();
        let root = self.k.name_str(anon, "subsetSearchControl");
        let leaf = format!("c{}", self.counter);
        self.k.name_str(root, &leaf)
    }

    /// Offer `value` to the trusted gate at type `ty`. `true` means the kernel
    /// ADMITTED it -- nothing here reads a boolean out of a checker of its own.
    fn admits(&mut self, ty: ExprId, value: ExprId) -> bool {
        let name = self.scratch();
        self.k
            .add_declaration(crate::env::Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
            .is_ok()
    }

    fn dev(&mut self) -> super::ops::NatDev<'_> {
        let p = self.p;
        super::ops::NatDev::new(&mut self.k, p)
    }

    fn bit_b(&mut self, k: u32, i: u32) -> ExprId {
        let kl = self.num(k);
        let il = self.num(i);
        let name = self.p.finset_bit_b;
        self.const_app(name, &[kl, il])
    }

    fn decode(&mut self, n: u32, k: u32) -> ExprId {
        let nl = self.num(n);
        let kl = self.num(k);
        let name = self.p.finset_decode;
        self.const_app(name, &[nl, kl])
    }

    fn encode(&mut self, t: ExprId, n: u32) -> ExprId {
        let nl = self.num(n);
        let name = self.p.finset_encode;
        self.const_app(name, &[t, nl])
    }

    fn encode_from(&mut self, f: ExprId, n: u32, j: u32) -> ExprId {
        let nl = self.num(n);
        let jl = self.num(j);
        let name = self.p.finset_encode_from;
        self.const_app(name, &[f, nl, jl])
    }

    fn any_subset(&mut self, big_p: ExprId, n: u32) -> ExprId {
        let nl = self.num(n);
        let name = self.p.finset_any_subset;
        self.const_app(name, &[big_p, nl])
    }

    fn mem(&mut self, s: ExprId, i: u32) -> ExprId {
        let lit = self.num(i);
        let name = self.p.finset_mem_b;
        self.const_app(name, &[s, lit])
    }

    fn card(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_card;
        self.const_app(name, &[s])
    }

    fn bound(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_bound;
        self.const_app(name, &[s])
    }

    fn singleton(&mut self, a: u32) -> ExprId {
        let lit = self.num(a);
        let name = self.p.finset_singleton;
        self.const_app(name, &[lit])
    }

    fn empty(&mut self) -> ExprId {
        let zero = self.zero();
        let name = self.p.finset_range;
        self.const_app(name, &[zero])
    }

    fn union(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_union;
        self.const_app(name, &[s, t])
    }

    /// `fun i => beq i target` -- a raw `Nat -> Bool` predicate.
    fn hits(&mut self, target: u32) -> ExprId {
        let nat = self.nat_ty();
        let lit = self.num(target);
        let i_fv = self.fresh_fvar();
        let i = self.k.fvar(i_fv);
        let body = self.beq(i, lit);
        self.lam_fv(i_fv, nat, body)
    }

    /// `fun t : Nat.Finset => beq (card t) size`.
    fn card_is(&mut self, size: u32) -> ExprId {
        let fs = {
            let name = self.p.finset;
            self.k.const_(name, vec![])
        };
        let lit = self.num(size);
        let t_fv = self.fresh_fvar();
        let t = self.k.fvar(t_fv);
        let c = self.card(t);
        let body = self.beq(c, lit);
        self.lam_fv(t_fv, fs, body)
    }

    fn assert_bool(&mut self, term: ExprId, expected: bool, message: &str) {
        let want = if expected {
            self.bool_true()
        } else {
            self.bool_false()
        };
        let other = if expected {
            self.bool_false()
        } else {
            self.bool_true()
        };
        assert!(self.k.def_eq(term, want), "{message}");
        assert!(
            !self.k.def_eq(term, other),
            "negative control: {message} -- must NOT reduce to the other Bool"
        );
    }

    fn assert_num(&mut self, term: ExprId, expected: u32, message: &str) {
        let want = self.num(expected);
        assert!(self.k.def_eq(term, want), "{message}");
    }

    fn assert_not_num(&mut self, term: ExprId, wrong: u32, message: &str) {
        let bad = self.num(wrong);
        assert!(!self.k.def_eq(term, bad), "negative control: {message}");
    }
}

// ---------------------------------------------------------------------------
// The definitions, at concrete small arguments.
// ---------------------------------------------------------------------------

/// `Nat.Finset.bitB` is the binary digit, and `1`-valued digits are `true`.
///
/// `5 = 0b101`, so bits `0` and `2` are set and bits `1` and `3` are not. A
/// `bitB` that compared `testBit` against `0` instead of `1` would answer the
/// exact opposite at all four indices, which is what the paired negative half
/// of every `assert_bool` rules out.
#[test]
fn bit_b_reads_the_binary_digit() {
    let mut f = Fixture::new();
    for (index, expected) in [(0u32, true), (1, false), (2, true), (3, false)] {
        let b = f.bit_b(5, index);
        let message = format!("bit {index} of 5 (0b101)");
        f.assert_bool(b, expected, &message);
    }
}

/// `Nat.Finset.decode n` enumerates the `2^n` subsets of `[0, n)`, in binary
/// order, and TRUNCATES at the width.
///
/// At `n = 2` the four codes give `{}`, `{0}`, `{1}`, `{0,1}` in that order —
/// so an encoder that wrote bit `0` for the largest index would swap the middle
/// two. And `decode 2 7` is `{0,1}`, not `{0,1,2}`: `7` has bit `2` set but the
/// set's bound is `2`, and `memB` truncates inside its own definition. `card`
/// pins that at `2`, with `3` named as the answer a non-truncating decode gives.
#[test]
fn decode_enumerates_the_subsets_and_truncates_at_the_width() {
    let mut f = Fixture::new();
    let table: [(u32, [bool; 2]); 4] = [
        (0, [false, false]),
        (1, [true, false]),
        (2, [false, true]),
        (3, [true, true]),
    ];
    for (code, members) in table {
        let sub = f.decode(2, code);
        let b = f.bound(sub);
        let message = format!("bound (decode 2 {code})");
        f.assert_num(b, 2, &message);
        for (index, expected) in members.iter().copied().enumerate() {
            let index = u32::try_from(index).expect("small index");
            let sub = f.decode(2, code);
            let m = f.mem(sub, index);
            let message = format!("{index} in decode 2 {code}");
            f.assert_bool(m, expected, &message);
        }
    }

    // Truncation: `7` sets bit `2`, but the width is `2`.
    let wide = f.decode(2, 7);
    let outside = f.mem(wide, 2);
    f.assert_bool(
        outside,
        false,
        "decode truncates at its width -- index 2 is not a member at width 2",
    );
    let wide = f.decode(2, 7);
    let c = f.card(wide);
    f.assert_num(c, 2, "card (decode 2 7) counts only the truncated members");
    let wide = f.decode(2, 7);
    let c = f.card(wide);
    f.assert_not_num(
        c,
        3,
        "3 is what a decode that did not inherit memB's truncation would give",
    );
}

/// `Nat.Finset.encode` is `decode`'s inverse, and the bit ORDER is index `i`
/// into bit `i`.
///
/// `{0}` codes as `1` and `{1}` as `2`. Each is named as the other's negative
/// control, because a reversed bit order — the single most likely wrong
/// formula, and one with exactly the same type — swaps precisely these two.
#[test]
fn encode_inverts_decode_at_width_two() {
    let mut f = Fixture::new();

    let e = f.empty();
    let code = f.encode(e, 2);
    f.assert_num(code, 0, "the empty set codes as 0");

    let lo = f.singleton(0);
    let code = f.encode(lo, 2);
    f.assert_num(code, 1, "{{0}} codes as 1");
    let lo = f.singleton(0);
    let code = f.encode(lo, 2);
    f.assert_not_num(code, 2, "2 is what a reversed bit order would give");

    let hi = f.singleton(1);
    let code = f.encode(hi, 2);
    f.assert_num(code, 2, "{{1}} codes as 2");
    let hi = f.singleton(1);
    let code = f.encode(hi, 2);
    f.assert_not_num(code, 1, "1 is what a reversed bit order would give");

    let both = {
        let a = f.singleton(0);
        let b = f.singleton(1);
        f.union(a, b)
    };
    let code = f.encode(both, 2);
    f.assert_num(code, 3, "{{0,1}} codes as 3");

    // The round trip, at concrete arguments: `decode 2 (encode t 2)` has the
    // same members as `t`.
    for (member, present) in [(0u32, false), (1, true)] {
        let hi = f.singleton(1);
        let code = f.encode(hi, 2);
        let two = f.num(2);
        let name = f.p.finset_decode;
        let back = f.const_app(name, &[two, code]);
        let m = f.mem(back, member);
        let message = format!("round trip at index {member} of {{1}}");
        f.assert_bool(m, present, &message);
    }
}

/// `Nat.Finset.encodeFrom` starts reading at its index argument and walks it
/// UPWARD.
///
/// With `f = fun i => beq i 1`, reading two bits from `0` finds the hit at
/// index `1`, so the code is `2`; reading two bits from `1` finds it
/// immediately, so the code is `1`. Each is the other's negative control: an
/// `encodeFrom` that decremented the start index, or that wrote the first bit
/// read into the highest position, would exchange them.
#[test]
fn encode_from_starts_at_its_index_and_walks_upward() {
    let mut f = Fixture::new();

    let pred = f.hits(1);
    let code = f.encode_from(pred, 2, 0);
    f.assert_num(code, 2, "reading [0,2) finds the hit at index 1");
    let pred = f.hits(1);
    let code = f.encode_from(pred, 2, 0);
    f.assert_not_num(code, 1, "1 is what reading the bits in reverse would give");

    let pred = f.hits(1);
    let code = f.encode_from(pred, 2, 1);
    f.assert_num(code, 1, "reading [1,3) finds the hit immediately");
    let pred = f.hits(1);
    let code = f.encode_from(pred, 2, 1);
    f.assert_not_num(code, 2, "2 is what starting one index lower would give");

    // Width `0` reads nothing at all.
    let pred = f.hits(1);
    let code = f.encode_from(pred, 0, 1);
    f.assert_num(code, 0, "width 0 reads no bits");
}

/// `Nat.Finset.anySubset` is the bounded EXISTENTIAL over subsets, not the
/// universal.
///
/// At width `2` exactly one of the four subsets has card `2`, and none has card
/// `3`. The pair is the discriminating check: an `anySubset` that dropped one
/// of its two negations would be `false` on the first (not every subset has
/// card `2`) and `true` on nothing, so it fails here in both directions.
#[test]
fn any_subset_is_the_existential_over_subsets() {
    let mut f = Fixture::new();

    let pred = f.card_is(2);
    let found = f.any_subset(pred, 2);
    f.assert_bool(found, true, "{{0,1}} has card 2, so anySubset is true");

    let pred = f.card_is(3);
    let missed = f.any_subset(pred, 2);
    f.assert_bool(
        missed,
        false,
        "no subset of [0,2) has card 3, so anySubset is false",
    );

    // At width `0` there is exactly one subset, the empty one.
    let pred = f.card_is(0);
    let found = f.any_subset(pred, 0);
    f.assert_bool(found, true, "the empty set is the only subset at width 0");
    let pred = f.card_is(1);
    let missed = f.any_subset(pred, 0);
    f.assert_bool(missed, false, "no subset at width 0 has card 1");
}

/// `Nat.strongInduction` computes: it is a recursor, not an opaque constant.
///
/// The step ignores its recursive argument, so no `Lt` proof is needed to
/// evaluate — but `WellFounded.fix` still has to reduce its accessibility proof
/// at the numeral for anything to come out, which is exactly what an
/// unreducible wrapper would fail to do.
#[test]
fn strong_induction_computes_at_a_numeral() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.level_one();
    let value = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let anon = d.anon_name();
        let motive = d.kernel().lam(anon, nat, nat, crate::BinderInfo::Default);
        let step = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let ih_fv = d.fresh_fvar();
            let ih_ty = {
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let hm_fv = d.fresh_fvar();
                let hm_ty = d.lt(m, n);
                let with_hm = d.pi_fv(hm_fv, hm_ty, nat);
                d.pi_fv(m_fv, nat, with_hm)
            };
            let body = d.succ(n);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            d.lam_fv(n_fv, nat, with_ih)
        };
        let three = d.num(3);
        let si = d.kernel().const_(p.strong_induction, vec![one]);
        d.apply(si, &[motive, step, three])
    };
    f.assert_num(value, 4, "strongInduction must reduce through the step");
    f.assert_not_num(value, 3, "3 is what a step returning `n` would give");
}

// ---------------------------------------------------------------------------
// The theorems: each admitted at its statement, rejected one small term away.
// ---------------------------------------------------------------------------

/// `Nat.Finset.bitB_encodeFrom` reads bit `i` as `f (j + i)`, in that order.
///
/// The rejected control swaps the two summands. `Nat.add` recurses on its right
/// argument, so `add i j` and `add j i` are not definitionally equal at
/// variables — the slide is one term and it is visible to the gate.
#[test]
fn bit_b_encode_from_is_admitted_and_the_transposed_sum_is_not() {
    let mut f = Fixture::new();
    let build = |f: &mut Fixture, forward: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let bool_ty = d.bool_ty();
        let pty = d.arrow(nat, bool_ty);
        let fn_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(fn_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.lt(i, n);
        let code = d.const_app(p.finset_encode_from, &[pred, n, j]);
        let lhs = d.const_app(p.finset_bit_b, &[code, i]);
        let shifted = if forward { d.add(j, i) } else { d.add(i, j) };
        let rhs = d.apply(pred, &[shifted]);
        let concl = d.bool_eq(lhs, rhs);
        let ty = {
            let with_hi = d.arrow(hi_ty, concl);
            let with_i = d.pi_fv(i_fv, nat, with_hi);
            let with_j = d.pi_fv(j_fv, nat, with_i);
            let with_n = d.pi_fv(n_fv, nat, with_j);
            d.pi_fv(fn_fv, pty, with_n)
        };
        let value = d.kernel().const_(p.finset_bit_b_encode_from, vec![]);
        (ty, value)
    };

    let (ty, value) = build(&mut f, true);
    assert!(f.admits(ty, value), "bitB_encodeFrom must be admitted");
    let (ty, value) = build(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: the transposed sum `f (i + j)` must be rejected"
    );
}

/// `Nat.Finset.encodeFrom_lt_pow` bounds the code by `pow 2 n`, where `n` is
/// the WIDTH.
///
/// The rejected control exchanges the width with the start index — one term,
/// and false as soon as the start index is smaller than the width.
#[test]
fn encode_from_lt_pow_is_admitted_and_the_swapped_width_is_not() {
    let mut f = Fixture::new();
    let build = |f: &mut Fixture, forward: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let bool_ty = d.bool_ty();
        let pty = d.arrow(nat, bool_ty);
        let fn_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(fn_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let code = if forward {
            d.const_app(p.finset_encode_from, &[pred, n, j])
        } else {
            d.const_app(p.finset_encode_from, &[pred, j, n])
        };
        let two = d.num(2);
        let range = d.pow(two, n);
        let concl = d.lt(code, range);
        let ty = {
            let with_j = d.pi_fv(j_fv, nat, concl);
            let with_n = d.pi_fv(n_fv, nat, with_j);
            d.pi_fv(fn_fv, pty, with_n)
        };
        let value = d.kernel().const_(p.finset_encode_from_lt_pow, vec![]);
        (ty, value)
    };

    let (ty, value) = build(&mut f, true);
    assert!(f.admits(ty, value), "encodeFrom_lt_pow must be admitted");
    let (ty, value) = build(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: the width and the start index are not interchangeable"
    );
}

/// `Nat.Finset.memB_decode_encode` needs `bound t ≤ n`, not `n ≤ bound t`.
///
/// The rejected control reverses that one inequality. It is not a technicality:
/// with the bound larger than the width the encoding loses every member above
/// `n`, so the theorem is FALSE in that direction, and the gate says so.
#[test]
fn mem_b_decode_encode_is_admitted_and_the_reversed_bound_is_not() {
    let mut f = Fixture::new();
    let build = |f: &mut Fixture, forward: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound_t = d.const_app(p.finset_bound, &[t]);
        let hb_ty = if forward {
            d.le(bound_t, n)
        } else {
            d.le(n, bound_t)
        };
        let code = d.const_app(p.finset_encode, &[t, n]);
        let sub = d.const_app(p.finset_decode, &[n, code]);
        let lhs = d.const_app(p.finset_mem_b, &[sub, i]);
        let rhs = d.const_app(p.finset_mem_b, &[t, i]);
        let concl = d.bool_eq(lhs, rhs);
        let ty = {
            let with_hb = d.arrow(hb_ty, concl);
            let with_i = d.pi_fv(i_fv, nat, with_hb);
            let with_n = d.pi_fv(n_fv, nat, with_i);
            d.pi_fv(t_fv, fs, with_n)
        };
        let value = d.kernel().const_(p.finset_mem_b_decode_encode, vec![]);
        (ty, value)
    };

    let (ty, value) = build(&mut f, true);
    assert!(f.admits(ty, value), "memB_decode_encode must be admitted");
    let (ty, value) = build(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: `Le n (bound t)` is the wrong direction and must be rejected"
    );
}

/// The reflection lemma, in both polarities, each with the OTHER polarity as
/// its negative control.
///
/// `existsSubset_of_search` consumes a `true` verdict and
/// `forallSubset_of_search` a `false` one. Offering each proof term at the
/// other's hypothesis is a one-constructor slide, and both must be rejected —
/// which is the check that the two lemmas really are two lemmas and not one
/// statement written twice.
#[test]
fn the_reflection_lemma_is_admitted_in_both_polarities_and_not_when_swapped() {
    let mut f = Fixture::new();

    let build_exists = |f: &mut Fixture, verdict: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let bool_ty = d.bool_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let big_p_ty = d.arrow(fs, bool_ty);
        let big_p_fv = d.fresh_fvar();
        let big_p = d.kernel().fvar(big_p_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let result_pred = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let bound_t = d.const_app(p.finset_bound, &[t]);
            let bound_eq = d.eq(bound_t, n);
            let at_t = d.apply(big_p, &[t]);
            let tv = d.bool_true();
            let val_eq = d.bool_eq(at_t, tv);
            let body = d.const_app(p.logic.and, &[bound_eq, val_eq]);
            d.lam_fv(t_fv, fs, body)
        };
        let one = d.level_one();
        let ex = d.kernel().const_(p.logic.exists_, vec![one]);
        let goal = d.apply(ex, &[fs, result_pred]);
        let search = d.const_app(p.finset_any_subset, &[big_p, n]);
        let literal = if verdict {
            d.bool_true()
        } else {
            d.bool_false()
        };
        let hyp_ty = d.bool_eq(search, literal);
        let ty = {
            let with_h = d.arrow(hyp_ty, goal);
            let with_n = d.pi_fv(n_fv, nat, with_h);
            d.pi_fv(big_p_fv, big_p_ty, with_n)
        };
        let value = d.kernel().const_(p.finset_exists_subset_of_search, vec![]);
        (ty, value)
    };

    let (ty, value) = build_exists(&mut f, true);
    assert!(
        f.admits(ty, value),
        "existsSubset_of_search must be admitted at a `true` verdict"
    );
    let (ty, value) = build_exists(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: a `false` verdict does not produce a witness"
    );

    let build_forall = |f: &mut Fixture, verdict: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let bool_ty = d.bool_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let big_p_ty = d.arrow(fs, bool_ty);
        let big_p_fv = d.fresh_fvar();
        let big_p = d.kernel().fvar(big_p_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let cong_ty = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let agree = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let lhs = d.const_app(p.finset_mem_b, &[u, i]);
                let rhs = d.const_app(p.finset_mem_b, &[v, i]);
                let body = d.bool_eq(lhs, rhs);
                d.pi_fv(i_fv, nat, body)
            };
            let at_u = d.apply(big_p, &[u]);
            let at_v = d.apply(big_p, &[v]);
            let concl = d.bool_eq(at_u, at_v);
            let with_agree = d.arrow(agree, concl);
            let with_v = d.pi_fv(v_fv, fs, with_agree);
            d.pi_fv(u_fv, fs, with_v)
        };
        let search = d.const_app(p.finset_any_subset, &[big_p, n]);
        let literal = if verdict {
            d.bool_false()
        } else {
            d.bool_true()
        };
        let hyp_ty = d.bool_eq(search, literal);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let bound_t = d.const_app(p.finset_bound, &[t]);
        let hb_ty = d.le(bound_t, n);
        let at_t = d.apply(big_p, &[t]);
        let fal = d.bool_false();
        let concl = d.bool_eq(at_t, fal);
        let ty = {
            let with_hb = d.arrow(hb_ty, concl);
            let with_t = d.pi_fv(t_fv, fs, with_hb);
            let with_h = d.arrow(hyp_ty, with_t);
            let with_hc = d.arrow(cong_ty, with_h);
            let with_n = d.pi_fv(n_fv, nat, with_hc);
            d.pi_fv(big_p_fv, big_p_ty, with_n)
        };
        let value = d.kernel().const_(p.finset_forall_subset_of_search, vec![]);
        (ty, value)
    };

    let (ty, value) = build_forall(&mut f, true);
    assert!(
        f.admits(ty, value),
        "forallSubset_of_search must be admitted at a `false` verdict"
    );
    let (ty, value) = build_forall(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: a `true` verdict refutes nothing"
    );
}

/// `Nat.Finset.card_congr_of_memB` needs membership agreement at EVERY index,
/// not only below the first set's bound.
///
/// The rejected control weakens the hypothesis to `Lt i (bound u) -> ...`. That
/// is not a technicality: with agreement only below `bound u`, `v` may carry
/// members above it and have a strictly larger card, so the theorem is FALSE in
/// that form -- and the gate says so, because the proof instantiates its
/// hypothesis over the common bound `bound u + bound v`.
#[test]
fn card_congr_of_mem_b_is_admitted_and_the_bounded_hypothesis_is_not() {
    let mut f = Fixture::new();
    let build = |f: &mut Fixture, forward: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let hyp_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lhs = d.const_app(p.finset_mem_b, &[u, i]);
            let rhs = d.const_app(p.finset_mem_b, &[v, i]);
            let body = d.bool_eq(lhs, rhs);
            let body = if forward {
                body
            } else {
                let bu = d.const_app(p.finset_bound, &[u]);
                let hi_ty = d.lt(i, bu);
                d.arrow(hi_ty, body)
            };
            d.pi_fv(i_fv, nat, body)
        };
        let card_u = d.const_app(p.finset_card, &[u]);
        let card_v = d.const_app(p.finset_card, &[v]);
        let concl = d.eq(card_u, card_v);
        let ty = {
            let with_h = d.arrow(hyp_ty, concl);
            let with_v = d.pi_fv(v_fv, fs, with_h);
            d.pi_fv(u_fv, fs, with_v)
        };
        let value = d.kernel().const_(p.finset_card_congr_of_mem_b, vec![]);
        (ty, value)
    };

    let (ty, value) = build(&mut f, true);
    assert!(f.admits(ty, value), "card_congr_of_memB must be admitted");
    let (ty, value) = build(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: agreement only below `bound u` does not fix the card"
    );
}

/// `Nat.strongInduction_eq` unfolds the fixpoint at `n`, not at some other
/// point.
///
/// The rejected control unfolds at `succ n` on the left and `n` on the right —
/// one `succ`, and the smallest slide that separates the equation from a
/// different one.
#[test]
fn strong_induction_eq_is_admitted_and_a_shifted_unfolding_is_not() {
    let mut f = Fixture::new();
    let build = |f: &mut Fixture, forward: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let one = f.level_one();
        let mut d = f.dev();
        let nat = d.nat_ty();
        let sort_one = d.kernel().sort(one);
        let motive_ty = d.arrow(nat, sort_one);
        let motive_fv = d.fresh_fvar();
        let motive = d.kernel().fvar(motive_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let step_ty = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let recursive = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let hq_fv = d.fresh_fvar();
                let hq_ty = d.lt(q, m);
                let at_q = d.apply(motive, &[q]);
                let with_hq = d.pi_fv(hq_fv, hq_ty, at_q);
                d.pi_fv(q_fv, nat, with_hq)
            };
            let at_m = d.apply(motive, &[m]);
            let body = d.arrow(recursive, at_m);
            d.pi_fv(m_fv, nat, body)
        };
        let step_fv = d.fresh_fvar();
        let step = d.kernel().fvar(step_fv);
        let si = d.kernel().const_(p.strong_induction, vec![one]);
        let point = if forward { n } else { d.succ(n) };
        let lhs = d.apply(si, &[motive, step, point]);
        let recursive = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let hm_fv = d.fresh_fvar();
            let hm_ty = d.lt(m, n);
            let at_m = d.apply(si, &[motive, step, m]);
            let with_hm = d.lam_fv(hm_fv, hm_ty, at_m);
            d.lam_fv(m_fv, nat, with_hm)
        };
        let rhs = d.apply(step, &[n, recursive]);
        let carrier = d.apply(motive, &[n]);
        let eq_const = d.kernel().const_(p.logic.eq, vec![one]);
        let concl = d.apply(eq_const, &[carrier, lhs, rhs]);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, concl);
            let with_step = d.pi_fv(step_fv, step_ty, with_n);
            d.pi_fv(motive_fv, motive_ty, with_step)
        };
        let value = d.kernel().const_(p.strong_induction_eq, vec![one]);
        (ty, value)
    };

    let (ty, value) = build(&mut f, true);
    assert!(f.admits(ty, value), "strongInduction_eq must be admitted");
    let (ty, value) = build(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: unfolding at `succ n` while recursing below `n` \
         is a different equation and must be rejected"
    );
}
