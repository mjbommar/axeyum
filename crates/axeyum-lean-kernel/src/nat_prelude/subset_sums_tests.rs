//! Concrete-instance tests for `nat_prelude::subset_sums`.
//!
//! The trusted gate cannot tell you a `Definition` is wrong — `empty`,
//! `insertAt`, `sumSubsets`, `sumSel` and `sumSelPos` are admitted on their
//! TYPE, and a fold that enumerated each subset twice, or that called the empty
//! set odd, has exactly the same type. So each is reduced here at tiny
//! arguments and paired with the wrong answer it rules out:
//!
//! * a `sumSubsets` that recursed on the width but reused the SAME half twice
//!   would count `2^n` subsets and still get every cardinality wrong;
//! * a fold that dropped the "without `n`" half would give `sumSubsets 2 card`
//!   the value `3`, not `4`;
//! * **the coordinated mutant**: `sumSel`'s base with its two branches
//!   exchanged — the empty set counted as ODD. Every algebraic law in the
//!   module except the two `sumSelPos` bridges stays TRUE under it (the graded
//!   pair is merely swapped), so it is the mutant that reaches the evaluation
//!   tests, and `sumSel 1 (fun s => if s 0 then 7 else 2) true = 2` is the
//!   assertion that names its wrong answer `7`.
//!
//! Every theorem is offered to the trusted gate twice: once at its real
//! statement (must be ADMITTED) and once at a statement slid by one small term
//! (must be REJECTED). Widths stay at `n ≤ 3`: every `Nat` numeral in this
//! prelude is unary and the fold visits `2^n` subsets.

use super::ops::{NatDev, NatOps};
use super::subset_sums::{
    empty_set, insert_at, set_ty, sum_sel, sum_sel_pos, sum_subsets, summand_ty, supported,
    with_top,
};
use crate::expr::ExprId;
use crate::{Kernel, NameId, NatPrelude, NatState, build_nat_prelude};

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
    fn scratch(&mut self) -> NameId {
        self.counter += 1;
        let anon = self.k.anon();
        let root = self.k.name_str(anon, "subsetSumsControl");
        let leaf = format!("c{}", self.counter);
        self.k.name_str(root, &leaf)
    }

    /// Offer `value` to the trusted gate at type `ty`. `true` means the kernel
    /// ADMITTED it — nothing here reads a boolean out of a checker of its own.
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

    /// Offer the already-declared theorem `thm` at the statement `ty`.
    fn thm_admits_at(&mut self, thm: NameId, ty: ExprId) -> bool {
        let value = self.k.const_(thm, vec![]);
        self.admits(ty, value)
    }

    fn dev(&mut self) -> NatDev<'_> {
        let p = self.p;
        NatDev::new(&mut self.k, p)
    }

    fn assert_num(&mut self, term: ExprId, expected: u32, message: &str) {
        let want = self.num(expected);
        assert!(self.k.def_eq(term, want), "{message}");
    }

    fn assert_not_num(&mut self, term: ExprId, wrong: u32, message: &str) {
        let bad = self.num(wrong);
        assert!(!self.k.def_eq(term, bad), "negative control: {message}");
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
            "negative control: {message} — must NOT reduce to the other Bool"
        );
    }
}

// ---------------------------------------------------------------------------
// Term builders over the fixture's kernel.
// ---------------------------------------------------------------------------

/// The subset `{a_0, …}`, as `insertAt a_k (… (insertAt a_0 empty))`.
fn set_of(d: &mut NatDev<'_>, p: &NatPrelude, members: &[u32]) -> ExprId {
    let p = *p;
    let mut s = empty_set(d, &p);
    for &m in members {
        let lit = d.num(m);
        s = insert_at(d, &p, lit, s);
    }
    s
}

/// `fun s => countRange s w` — the number of members below `w`.
fn count_below(d: &mut NatDev<'_>, p: &NatPrelude, w: u32) -> ExprId {
    let sty = set_ty(d);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let lit = d.num(w);
    let body = d.const_app(p.count_range, &[s, lit]);
    d.lam_fv(s_fv, sty, body)
}

/// `fun _ => c`.
fn const_summand(d: &mut NatDev<'_>, c: u32) -> ExprId {
    let sty = set_ty(d);
    let s_fv = d.fresh_fvar();
    let lit = d.num(c);
    d.lam_fv(s_fv, sty, lit)
}

/// `fun s => if s i then hi else lo` — a summand that DISTINGUISHES the two
/// parities, unlike a constant one.
fn weighted(d: &mut NatDev<'_>, i: u32, hi: u32, lo: u32) -> ExprId {
    let sty = set_ty(d);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let idx = d.num(i);
    let cond = d.apply(s, &[idx]);
    let hi_lit = d.num(hi);
    let lo_lit = d.num(lo);
    let body = d.bool_select_nat(cond, hi_lit, lo_lit);
    d.lam_fv(s_fv, sty, body)
}

/// `fun s => (if s 0 then 1 else 0) * (if s 1 then 1 else 0)` — the indicator
/// of `{0,1} ⊆ s`.
fn both_of_two(d: &mut NatDev<'_>) -> ExprId {
    let sty = set_ty(d);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let zero = d.zero();
    let one = d.num(1);
    let at0 = d.apply(s, &[zero]);
    let one_a = d.num(1);
    let zero_a = d.zero();
    let left = d.bool_select_nat(at0, one_a, zero_a);
    let at1 = d.apply(s, &[one]);
    let one_b = d.num(1);
    let zero_b = d.zero();
    let right = d.bool_select_nat(at1, one_b, zero_b);
    let body = d.mul(left, right);
    d.lam_fv(s_fv, sty, body)
}

// ---------------------------------------------------------------------------
// The definitions, at concrete small arguments.
// ---------------------------------------------------------------------------

/// `Nat.Subsets.empty` has no members, and `insertAt` adds EXACTLY its index.
///
/// The wrong readings this rules out: an `insertAt` that inserted at `succ n`
/// would put `2` into `insertAt 1 empty` and leave `1` out, and one that
/// replaced rather than added would drop `0` from `{0,1}`.
#[test]
fn insert_at_adds_exactly_its_index() {
    let mut f = Fixture::new();
    let p = f.p;

    for index in 0..3u32 {
        let term = {
            let mut d = f.dev();
            let e = empty_set(&mut d, &p);
            let lit = d.num(index);
            d.apply(e, &[lit])
        };
        let message = format!("{index} in Nat.Subsets.empty");
        f.assert_bool(term, false, &message);
    }

    let table: [(u32, bool); 3] = [(0, false), (1, true), (2, false)];
    for (index, expected) in table {
        let term = {
            let mut d = f.dev();
            let s = set_of(&mut d, &p, &[1]);
            let lit = d.num(index);
            d.apply(s, &[lit])
        };
        let message = format!("{index} in insertAt 1 empty");
        f.assert_bool(term, expected, &message);
    }

    let table: [(u32, bool); 3] = [(0, true), (1, true), (2, false)];
    for (index, expected) in table {
        let term = {
            let mut d = f.dev();
            let s = set_of(&mut d, &p, &[0, 1]);
            let lit = d.num(index);
            d.apply(s, &[lit])
        };
        let message = format!("{index} in {{0,1}}");
        f.assert_bool(term, expected, &message);
    }
}

/// `sumSubsets n F` visits every subset of `[0,n)` exactly once.
///
/// At `n = 2` with `F = card` the four subsets contribute `0 + 1 + 1 + 2 = 4`.
/// A fold that dropped the "without `n`" half would give `3`; one that visited
/// a subset twice would give more than `4`. `sumSubsets n (fun _ => 1) = 2^n`
/// pins the COUNT separately, at `n = 0, 1, 2, 3`.
#[test]
fn sum_subsets_visits_every_subset_once() {
    let mut f = Fixture::new();
    let p = f.p;

    let total = {
        let mut d = f.dev();
        let card = count_below(&mut d, &p, 2);
        let two = d.num(2);
        sum_subsets(&mut d, &p, two, card)
    };
    f.assert_num(total, 4, "sumSubsets 2 card = 0 + 1 + 1 + 2");
    f.assert_not_num(total, 3, "a fold dropping the without-n half would give 3");
    f.assert_not_num(total, 6, "a fold visiting {0,1} twice would give 6");

    for (n, expected) in [(0u32, 1u32), (1, 2), (2, 4), (3, 8)] {
        let count = {
            let mut d = f.dev();
            let ones = const_summand(&mut d, 1);
            let lit = d.num(n);
            sum_subsets(&mut d, &p, lit, ones)
        };
        let message = format!("sumSubsets {n} (fun _ => 1) = 2^{n}");
        f.assert_num(count, expected, &message);
        f.assert_not_num(count, expected + 1, &message);
    }
}

/// `sumSel` grades by cardinality parity, and THE EMPTY SET IS EVEN.
///
/// This is the assertion the coordinated mutant fails. At `n = 1` the two
/// subsets are `∅` and `{0}`; with `F s = if s 0 then 7 else 2` the even sum is
/// `2` and the odd sum is `7`. A `sumSel` whose base exchanged its two branches
/// — the empty set called ODD — satisfies every algebraic law in the module
/// except the two `sumSelPos` bridges, and answers `7` and `2` here.
#[test]
fn sum_sel_grades_by_parity_and_the_empty_set_is_even() {
    let mut f = Fixture::new();
    let p = f.p;

    let even = {
        let mut d = f.dev();
        let g = weighted(&mut d, 0, 7, 2);
        let one = d.num(1);
        let tv = d.bool_true();
        sum_sel(&mut d, &p, one, g, tv)
    };
    f.assert_num(
        even,
        2,
        "sumSel 1 (fun s => if s 0 then 7 else 2) true = F ∅",
    );
    f.assert_not_num(
        even,
        7,
        "the coordinated mutant (∅ counted ODD) answers 7 here",
    );

    let odd = {
        let mut d = f.dev();
        let g = weighted(&mut d, 0, 7, 2);
        let one = d.num(1);
        let fal = d.bool_false();
        sum_sel(&mut d, &p, one, g, fal)
    };
    f.assert_num(odd, 7, "sumSel 1 … false = F {0}");
    f.assert_not_num(odd, 2, "the coordinated mutant answers 2 here");

    // At width 2 the even subsets are `∅` and `{0,1}`, the odd ones `{0}`,
    // `{1}`. Only `{0,1}` contains both, so the indicator sums are 1 and 0.
    let even2 = {
        let mut d = f.dev();
        let g = both_of_two(&mut d);
        let two = d.num(2);
        let tv = d.bool_true();
        sum_sel(&mut d, &p, two, g, tv)
    };
    f.assert_num(even2, 1, "only {0,1} is even and contains both");
    let odd2 = {
        let mut d = f.dev();
        let g = both_of_two(&mut d);
        let two = d.num(2);
        let fal = d.bool_false();
        sum_sel(&mut d, &p, two, g, fal)
    };
    f.assert_num(odd2, 0, "no odd subset of [0,2) contains both 0 and 1");
    f.assert_not_num(
        odd2,
        1,
        "an odd sum of 1 would mean a singleton contains both",
    );
}

/// `sumSelPos` is `sumSel` with the empty set removed — and the empty set is
/// the ONLY difference.
///
/// At `n = 2` over `fun _ => 1`: the non-empty even subsets are `{0,1}` (one of
/// them) and the odd ones are `{0}`, `{1}` (two). `sumSel` would answer `2` and
/// `2`. A `sumSelPos` that also dropped a singleton would answer `1` on the odd
/// side.
#[test]
fn sum_sel_pos_drops_the_empty_set_and_nothing_else() {
    let mut f = Fixture::new();
    let p = f.p;

    for (b, expected, plain) in [(true, 1u32, 2u32), (false, 2, 2)] {
        let pos = {
            let mut d = f.dev();
            let ones = const_summand(&mut d, 1);
            let two = d.num(2);
            let bv = if b { d.bool_true() } else { d.bool_false() };
            sum_sel_pos(&mut d, &p, two, ones, bv)
        };
        let message = format!("sumSelPos 2 (fun _ => 1) {b}");
        f.assert_num(pos, expected, &message);
        if expected != plain {
            f.assert_not_num(pos, plain, &message);
        }
    }

    let empty_width = {
        let mut d = f.dev();
        let ones = const_summand(&mut d, 1);
        let zero = d.zero();
        let tv = d.bool_true();
        sum_sel_pos(&mut d, &p, zero, ones, tv)
    };
    f.assert_num(empty_width, 0, "there is no non-empty subset of [0,0)");
    f.assert_not_num(empty_width, 1, "a sumSelPos that kept ∅ would answer 1");
}

// ---------------------------------------------------------------------------
// Accept/reject pairs: every theorem, at its real statement and at a slid one.
// ---------------------------------------------------------------------------

/// THE SPLIT LAW — `sumSubsets (succ n) F = sumSubsets n F +
/// sumSubsets n (F ∘ insertAt n)` — and the same proof term REJECTED with the
/// two halves exchanged.
///
/// The exchange is not defeq: `Nat.add` recurses on its right argument, so for
/// a symbolic `n` the two orders are different terms. That is the whole point
/// of the law being `Eq.refl` in one order and not the other — the recursion
/// enumerates the "without `n`" half FIRST, and a consumer that assumes the
/// other order gets a rejection rather than a wrong answer.
#[test]
fn the_split_law_is_admitted_and_the_exchanged_halves_are_not() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fty = summand_ty(&mut d);
        let build = |d: &mut NatDev<'_>, swapped: bool| -> ExprId {
            let f_fv = d.fresh_fvar();
            let ff = d.kernel().fvar(f_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let sn = d.succ(n);
            let lhs = sum_subsets(d, &p, sn, ff);
            let low = sum_subsets(d, &p, n, ff);
            let shifted = with_top(d, &p, ff, n);
            let high = sum_subsets(d, &p, n, shifted);
            let rhs = if swapped {
                d.add(high, low)
            } else {
                d.add(low, high)
            };
            let concl = d.eq(lhs, rhs);
            let with_n = d.pi_fv(n_fv, nat, concl);
            d.pi_fv(f_fv, fty, with_n)
        };
        let real = build(&mut d, false);
        let slid = build(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_sum_subsets_succ;
    assert!(
        f.thm_admits_at(name, real),
        "the split law must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the split law with its two halves exchanged must be REJECTED"
    );
}

/// The GRADED split law flips the parity on the "with `n`" half — and the same
/// proof term is REJECTED when the flip is dropped.
#[test]
fn the_graded_split_law_is_admitted_and_the_unflipped_parity_is_not() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let bool_ty = d.bool_ty();
        let fty = summand_ty(&mut d);
        let build = |d: &mut NatDev<'_>, flip: bool| -> ExprId {
            let f_fv = d.fresh_fvar();
            let ff = d.kernel().fvar(f_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let sn = d.succ(n);
            let lhs = sum_sel(d, &p, sn, ff, b);
            let low = sum_sel(d, &p, n, ff, b);
            let shifted = with_top(d, &p, ff, n);
            let parity = if flip {
                super::graph::not_b(d, &p, b)
            } else {
                b
            };
            let high = sum_sel(d, &p, n, shifted, parity);
            let rhs = d.add(low, high);
            let concl = d.eq(lhs, rhs);
            let with_b = d.pi_fv(b_fv, bool_ty, concl);
            let with_n = d.pi_fv(n_fv, nat, with_b);
            d.pi_fv(f_fv, fty, with_n)
        };
        let real = build(&mut d, true);
        let slid = build(&mut d, false);
        (real, slid)
    };

    let name = p.subsets_sum_sel_succ;
    assert!(
        f.thm_admits_at(name, real),
        "the graded split law must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: adding an element must FLIP the parity"
    );
}

/// `sumSel_zero` puts the empty set on the EVEN side — and the same proof term
/// is REJECTED with the two branches exchanged.
///
/// This is the accept/reject pair that pins the coordinated mutant at the level
/// of statements, as the evaluation test pins it at the level of values.
#[test]
fn the_empty_set_is_even_and_the_exchanged_branches_are_rejected() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let bool_ty = d.bool_ty();
        let fty = summand_ty(&mut d);
        let build = |d: &mut NatDev<'_>, exchanged: bool| -> ExprId {
            let f_fv = d.fresh_fvar();
            let ff = d.kernel().fvar(f_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let zero = d.zero();
            let lhs = sum_sel(d, &p, zero, ff, b);
            let e = empty_set(d, &p);
            let at_empty = d.apply(ff, &[e]);
            let z = d.zero();
            let rhs = if exchanged {
                d.bool_select_nat(b, z, at_empty)
            } else {
                d.bool_select_nat(b, at_empty, z)
            };
            let concl = d.eq(lhs, rhs);
            let with_b = d.pi_fv(b_fv, bool_ty, concl);
            d.pi_fv(f_fv, fty, with_b)
        };
        let real = build(&mut d, false);
        let slid = build(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_sum_sel_zero;
    assert!(
        f.thm_admits_at(name, real),
        "the empty set must sit on the even side"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the exchanged branches must be REJECTED"
    );
}

/// `sumSel_congr`'s hypothesis is at the width `n` — and the same proof term is
/// REJECTED at `succ n`.
///
/// The direction matters and is easy to get backwards: agreeing on the sets
/// supported below `succ n` is a STRONGER hypothesis than agreeing below `n`,
/// so the lemma as stated is the more useful one. Offering it at the stronger
/// hypothesis is not a soundness question, it is a usability one — and the
/// kernel refuses because the two statements are different terms.
#[test]
fn sum_sel_congr_is_admitted_and_the_shifted_support_is_not() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let bool_ty = d.bool_ty();
        let sty = set_ty(&mut d);
        let fty = summand_ty(&mut d);
        let build = |d: &mut NatDev<'_>, shifted: bool| -> ExprId {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let f_fv = d.fresh_fvar();
            let ff = d.kernel().fvar(f_fv);
            let g_fv = d.fresh_fvar();
            let gg = d.kernel().fvar(g_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let width = if shifted { d.succ(n) } else { n };
            let agree = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let sup = supported(d, &p, s, width);
                let fs = d.apply(ff, &[s]);
                let gs = d.apply(gg, &[s]);
                let eq = d.eq(fs, gs);
                let with_sup = d.arrow(sup, eq);
                d.pi_fv(s_fv, sty, with_sup)
            };
            let lhs = sum_sel(d, &p, n, ff, b);
            let rhs = sum_sel(d, &p, n, gg, b);
            let concl = d.eq(lhs, rhs);
            let with_agree = d.arrow(agree, concl);
            let with_b = d.pi_fv(b_fv, bool_ty, with_agree);
            let with_g = d.pi_fv(g_fv, fty, with_b);
            let with_f = d.pi_fv(f_fv, fty, with_g);
            d.pi_fv(n_fv, nat, with_f)
        };
        let real = build(&mut d, false);
        let slid = build(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_sum_sel_congr;
    assert!(
        f.thm_admits_at(name, real),
        "sumSel_congr must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the hypothesis at succ n must be REJECTED"
    );
}

/// `sumSel_mul_right` scales on the RIGHT — and the same proof term is REJECTED
/// with the product commuted.
#[test]
fn sum_sel_mul_right_is_admitted_and_the_commuted_product_is_not() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let bool_ty = d.bool_ty();
        let sty = set_ty(&mut d);
        let fty = summand_ty(&mut d);
        let build = |d: &mut NatDev<'_>, commuted: bool| -> ExprId {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let f_fv = d.fresh_fvar();
            let ff = d.kernel().fvar(f_fv);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let scaled = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let fs = d.apply(ff, &[s]);
                let body = d.mul(fs, c);
                d.lam_fv(s_fv, sty, body)
            };
            let lhs = sum_sel(d, &p, n, scaled, b);
            let plain = sum_sel(d, &p, n, ff, b);
            let rhs = if commuted {
                d.mul(c, plain)
            } else {
                d.mul(plain, c)
            };
            let concl = d.eq(lhs, rhs);
            let with_b = d.pi_fv(b_fv, bool_ty, concl);
            let with_c = d.pi_fv(c_fv, nat, with_b);
            let with_f = d.pi_fv(f_fv, fty, with_c);
            d.pi_fv(n_fv, nat, with_f)
        };
        let real = build(&mut d, false);
        let slid = build(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_sum_sel_mul_right;
    assert!(
        f.thm_admits_at(name, real),
        "sumSel_mul_right must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the commuted product must be REJECTED"
    );
}

/// `sumSel_add` sums the EVEN and ODD halves in that order — and the same proof
/// term is REJECTED with the two exchanged.
///
/// `sumSel_true_eq_empty_add_pos` is the other half of this pair: it is offered
/// at `false`, which is `sumSel_false_eq_pos`'s statement, and refused.
#[test]
fn the_grading_partitions_and_the_exchanged_or_reparitied_statements_do_not() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fty = summand_ty(&mut d);
        let build = |d: &mut NatDev<'_>, exchanged: bool| -> ExprId {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let f_fv = d.fresh_fvar();
            let ff = d.kernel().fvar(f_fv);
            let tv = d.bool_true();
            let fal = d.bool_false();
            let even = sum_sel(d, &p, n, ff, tv);
            let odd = sum_sel(d, &p, n, ff, fal);
            let lhs = if exchanged {
                d.add(odd, even)
            } else {
                d.add(even, odd)
            };
            let rhs = sum_subsets(d, &p, n, ff);
            let concl = d.eq(lhs, rhs);
            let with_f = d.pi_fv(f_fv, fty, concl);
            d.pi_fv(n_fv, nat, with_f)
        };
        let real = build(&mut d, false);
        let slid = build(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_sum_sel_add;
    assert!(
        f.thm_admits_at(name, real),
        "sumSel_add must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the exchanged halves must be REJECTED"
    );

    // `sumSel n F true = F empty + sumSelPos n F true`, offered at `false`.
    let (real_pos, slid_pos) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fty = summand_ty(&mut d);
        let build = |d: &mut NatDev<'_>, even: bool| -> ExprId {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let f_fv = d.fresh_fvar();
            let ff = d.kernel().fvar(f_fv);
            let parity = if even { d.bool_true() } else { d.bool_false() };
            let lhs = sum_sel(d, &p, n, ff, parity);
            let e = empty_set(d, &p);
            let at_empty = d.apply(ff, &[e]);
            let pos = sum_sel_pos(d, &p, n, ff, parity);
            let rhs = d.add(at_empty, pos);
            let concl = d.eq(lhs, rhs);
            let with_f = d.pi_fv(f_fv, fty, concl);
            d.pi_fv(n_fv, nat, with_f)
        };
        let real_pos = build(&mut d, true);
        let slid_pos = build(&mut d, false);
        (real_pos, slid_pos)
    };

    let name = p.subsets_sum_sel_true_split;
    assert!(
        f.thm_admits_at(name, real_pos),
        "the empty set is the even side's only extra term"
    );
    assert!(
        !f.thm_admits_at(name, slid_pos),
        "negative control: the same statement at ODD parity must be REJECTED"
    );
}

/// `supported_insertAt` widens the support to `succ n` — and the same proof term
/// is REJECTED at `n`.
///
/// `insertAt n s` really does have a member at `n`, so the un-widened
/// conclusion is FALSE, not merely differently spelled.
#[test]
fn supported_insert_at_widens_and_the_unwidened_conclusion_is_rejected() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let sty = set_ty(&mut d);
        let build = |d: &mut NatDev<'_>, widened: bool| -> ExprId {
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let hyp = supported(d, &p, s, n);
            let ins = insert_at(d, &p, n, s);
            let width = if widened { d.succ(n) } else { n };
            let concl = supported(d, &p, ins, width);
            let with_hyp = d.arrow(hyp, concl);
            let with_n = d.pi_fv(n_fv, nat, with_hyp);
            d.pi_fv(s_fv, sty, with_n)
        };
        let real = build(&mut d, true);
        let slid = build(&mut d, false);
        (real, slid)
    };

    let name = p.subsets_supported_insert_at;
    assert!(
        f.thm_admits_at(name, real),
        "supported_insertAt must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the un-widened conclusion must be REJECTED"
    );
}
