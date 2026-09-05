//! Concrete-instance tests for `nat_prelude::inclusion_exclusion`.
//!
//! The centrepiece is a THREE-set instance evaluated end to end. The family is
//! `A i = {i, i+1}` over the ambient range `[0,4)`, so
//!
//! ```text
//! A 0 = {0,1}   A 1 = {1,2}   A 2 = {2,3}     union = {0,1,2,3},  |union| = 4
//! singletons   |A 0| = |A 1| = |A 2| = 2                 odd sum  = 6
//! pairs        |A 0 ∩ A 1| = 1, |A 0 ∩ A 2| = 0, |A 1 ∩ A 2| = 1  even sum = 2
//! triple       |A 0 ∩ A 1 ∩ A 2| = 0                     odd sum += 0
//! ```
//!
//! and `4 + 2 = 6` is inclusion–exclusion at `n = 3`. Every one of those seven
//! numbers is asserted separately, each against a named wrong answer, because a
//! `meetInd` that intersected the WRONG subset, or a `sumSelPos` that graded by
//! the wrong parity, would still make the totals match if only the totals were
//! checked.
//!
//! The trusted gate cannot tell you a `Definition` is wrong, so `anyOf`,
//! `noneOf`, `prodPar`, `meetInd`, `meetCard`, `unionAt`, `ieSum` and
//! `ieSumPos` are each reduced at small arguments as well. Widths stay at
//! `n ≤ 3` and the ambient range at `m ≤ 4`: every `Nat` numeral here is unary
//! and the fold visits `2^n` subsets, each summing over `m` elements.
//!
//! `inclusion_exclusion_two` gets a different kind of check. Its statement is
//! built once and offered to the trusted gate TWICE — once with the derived
//! theorem and once with `Nat.countRange_union_add_inter` applied at
//! `A 0`, `A 1` — so "the two-set case is recovered" is not a claim about two
//! similar-looking types, it is the kernel accepting the pre-existing lemma at
//! the derived one's statement.

use super::inclusion_exclusion::{
    any_of, ie_sum, ie_sum_pos, meet_card, meet_ind, none_of, prod_par, union_at,
};
use super::ops::{NatDev, NatOps};
use super::subset_sums::{bool_select_bool, empty_set, insert_at, set_ty};
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

    fn scratch(&mut self) -> NameId {
        self.counter += 1;
        let anon = self.k.anon();
        let root = self.k.name_str(anon, "inclusionExclusionControl");
        let leaf = format!("c{}", self.counter);
        self.k.name_str(root, &leaf)
    }

    /// Offer `value` to the trusted gate at type `ty`. `true` means the kernel
    /// ADMITTED it.
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
// The worked family.
// ---------------------------------------------------------------------------

/// `fun i v => if beq v i then true else beq v (succ i)` — the family
/// `A i = {i, i+1}`.
fn adjacent_pairs(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let hit_low = d.beq(v, i);
    let si = d.succ(i);
    let hit_high = d.beq(v, si);
    let tv = d.bool_true();
    let body = bool_select_bool(d, &p, hit_low, tv, hit_high);
    let with_v = d.lam_fv(v_fv, nat, body);
    d.lam_fv(i_fv, nat, with_v)
}

/// `fun i => beq i target` — a one-element `Nat → Bool`.
fn only(d: &mut NatDev<'_>, target: u32) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let lit = d.num(target);
    let body = d.beq(i, lit);
    d.lam_fv(i_fv, nat, body)
}

/// `fun _ => false`.
fn never(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let fal = d.bool_false();
    d.kernel()
        .lam(anon, nat, fal, crate::expr::BinderInfo::Default)
}

/// The subset of `[0,n)` with the listed members.
fn set_of(d: &mut NatDev<'_>, p: &NatPrelude, members: &[u32]) -> ExprId {
    let p = *p;
    let mut s = empty_set(d, &p);
    for &x in members {
        let lit = d.num(x);
        s = insert_at(d, &p, lit, s);
    }
    s
}

// ---------------------------------------------------------------------------
// The definitions, at concrete small arguments.
// ---------------------------------------------------------------------------

/// `anyOf c n` is `∃ i < n, c i`, and it reads the window `[0,n)` — not
/// `[0,n]`.
#[test]
fn any_of_is_the_bounded_existential() {
    let mut f = Fixture::new();
    let p = f.p;
    for (width, expected) in [(0u32, false), (1, false), (2, true), (3, true)] {
        let term = {
            let mut d = f.dev();
            let c = only(&mut d, 1);
            let lit = d.num(width);
            any_of(&mut d, &p, c, lit)
        };
        let message = format!("anyOf (fun i => beq i 1) {width}");
        f.assert_bool(term, expected, &message);
    }
}

/// `noneOf c n` is `1` exactly when `anyOf c n` is `false`.
#[test]
fn none_of_is_the_complementary_indicator() {
    let mut f = Fixture::new();
    let p = f.p;
    for (width, expected) in [(0u32, 1u32), (1, 1), (2, 0), (3, 0)] {
        let term = {
            let mut d = f.dev();
            let c = only(&mut d, 1);
            let lit = d.num(width);
            none_of(&mut d, &p, c, lit)
        };
        let message = format!("noneOf (fun i => beq i 1) {width}");
        f.assert_num(term, expected, &message);
        f.assert_not_num(term, 1 - expected, &message);
    }
}

/// `prodPar c n b` expands the product over the subsets of `[0,n)` of parity
/// `b`, and `prodPar_even`'s residue is visible in the numbers.
///
/// At `c = fun _ => false` only the empty subset contributes, so the even sum
/// is `1` and the odd sum `0` — and `noneOf c 2 = 1` closes `1 = 0 + 1`. At
/// `c = fun i => beq i 0` the subsets `∅` and `{0}` contribute `1` each, so
/// both sums are `1` and the residue is `0`.
#[test]
fn prod_par_expands_the_product_over_subsets() {
    let mut f = Fixture::new();
    let p = f.p;

    let table: [(bool, bool, u32); 4] = [
        (false, true, 1),
        (false, false, 0),
        (true, true, 1),
        (true, false, 1),
    ];
    for (hits_zero, even, expected) in table {
        let term = {
            let mut d = f.dev();
            let c = if hits_zero {
                only(&mut d, 0)
            } else {
                never(&mut d)
            };
            let two = d.num(2);
            let b = if even { d.bool_true() } else { d.bool_false() };
            prod_par(&mut d, &p, c, two, b)
        };
        let message = format!("prodPar (hits_zero={hits_zero}) 2 {even}");
        f.assert_num(term, expected, &message);
        f.assert_not_num(term, expected + 1, &message);
    }
}

/// The whole of inclusion–exclusion at THREE explicit sets, number by number.
///
/// `A i = {i, i+1}` over `[0,4)`. Each intersection's cardinality is asserted
/// on its own, so a `meetInd` that intersected a different subset would fail
/// here even if the totals happened to agree.
#[test]
fn three_explicit_sets_are_counted_subset_by_subset() {
    let mut f = Fixture::new();
    let p = f.p;

    // The eight subsets of `[0,3)` and the cardinality of the corresponding
    // intersection inside `[0,4)`.
    let table: [(&[u32], u32); 8] = [
        (&[], 4),
        (&[0], 2),
        (&[1], 2),
        (&[2], 2),
        (&[0, 1], 1),
        (&[0, 2], 0),
        (&[1, 2], 1),
        (&[0, 1, 2], 0),
    ];
    for (members, expected) in table {
        let term = {
            let mut d = f.dev();
            let a = adjacent_pairs(&mut d, &p);
            let s = set_of(&mut d, &p, members);
            let three = d.num(3);
            let four = d.num(4);
            meet_card(&mut d, &p, a, three, s, four)
        };
        let message = format!("|intersection over {members:?}| inside [0,4)");
        f.assert_num(term, expected, &message);
        f.assert_not_num(term, expected + 1, &message);
    }

    // The union covers the whole of `[0,4)`.
    let union_count = {
        let mut d = f.dev();
        let a = adjacent_pairs(&mut d, &p);
        let three = d.num(3);
        let four = d.num(4);
        let u = union_at(&mut d, &p, a, three);
        d.const_app(p.count_range, &[u, four])
    };
    f.assert_num(union_count, 4, "|A 0 ∪ A 1 ∪ A 2| inside [0,4)");
    f.assert_not_num(union_count, 3, "the union misses nothing in [0,4)");

    // The graded sums, non-empty subsets only: `4 + 2 = 6`.
    for (even, expected) in [(true, 2u32), (false, 6)] {
        let term = {
            let mut d = f.dev();
            let a = adjacent_pairs(&mut d, &p);
            let three = d.num(3);
            let four = d.num(4);
            let b = if even { d.bool_true() } else { d.bool_false() };
            ie_sum_pos(&mut d, &p, a, three, four, b)
        };
        let message = format!("ieSumPos A 3 4 {even}");
        f.assert_num(term, expected, &message);
        f.assert_not_num(term, expected + 1, &message);
    }

    // And the un-restricted sums, which carry the empty set's `4` on the even
    // side: `6 + 4 = 6 + 4`.
    for (even, expected) in [(true, 6u32), (false, 6)] {
        let term = {
            let mut d = f.dev();
            let a = adjacent_pairs(&mut d, &p);
            let three = d.num(3);
            let four = d.num(4);
            let b = if even { d.bool_true() } else { d.bool_false() };
            ie_sum(&mut d, &p, a, three, four, b)
        };
        let message = format!("ieSum A 3 4 {even}");
        f.assert_num(term, expected, &message);
        f.assert_not_num(term, expected + 1, &message);
    }
}

/// `meetInd` is the indicator of membership in EVERY listed set.
///
/// At `s = {0,1}` the only element of `[0,4)` in both `A 0 = {0,1}` and
/// `A 1 = {1,2}` is `1`.
#[test]
fn meet_ind_is_the_intersection_indicator() {
    let mut f = Fixture::new();
    let p = f.p;
    for (v, expected) in [(0u32, 0u32), (1, 1), (2, 0), (3, 0)] {
        let term = {
            let mut d = f.dev();
            let a = adjacent_pairs(&mut d, &p);
            let s = set_of(&mut d, &p, &[0, 1]);
            let three = d.num(3);
            let lit = d.num(v);
            meet_ind(&mut d, &p, a, three, s, lit)
        };
        let message = format!("{v} in A 0 ∩ A 1");
        f.assert_num(term, expected, &message);
        f.assert_not_num(term, 1 - expected, &message);
    }
}

// ---------------------------------------------------------------------------
// Accept/reject pairs.
// ---------------------------------------------------------------------------

/// The general theorem is admitted, and REJECTED with its two right-hand
/// summands exchanged.
#[test]
fn inclusion_exclusion_is_admitted_and_the_exchanged_right_side_is_not() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let cty = set_ty(&mut d);
        let fam = d.arrow(nat, cty);
        let build = |d: &mut NatDev<'_>, exchanged: bool| -> ExprId {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let tv = d.bool_true();
            let fal = d.bool_false();
            let even = ie_sum(d, &p, a, n, m, tv);
            let odd = ie_sum(d, &p, a, n, m, fal);
            let u = union_at(d, &p, a, n);
            let cu = d.const_app(p.count_range, &[u, m]);
            let lhs = d.add(even, cu);
            let rhs = if exchanged {
                d.add(m, odd)
            } else {
                d.add(odd, m)
            };
            let concl = d.eq(lhs, rhs);
            let with_m = d.pi_fv(m_fv, nat, concl);
            let with_n = d.pi_fv(n_fv, nat, with_m);
            d.pi_fv(a_fv, fam, with_n)
        };
        let real = build(&mut d, false);
        let slid = build(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_inclusion_exclusion;
    assert!(
        f.thm_admits_at(name, real),
        "general inclusion–exclusion must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the exchanged right-hand summands must be REJECTED"
    );
}

/// The classical (non-empty-subsets) form is admitted, and REJECTED with the
/// two parities exchanged.
#[test]
fn the_positive_form_is_admitted_and_the_swapped_parities_are_not() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let cty = set_ty(&mut d);
        let fam = d.arrow(nat, cty);
        let build = |d: &mut NatDev<'_>, swapped: bool| -> ExprId {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let tv = d.bool_true();
            let fal = d.bool_false();
            let (left, right) = if swapped { (fal, tv) } else { (tv, fal) };
            let even = ie_sum_pos(d, &p, a, n, m, left);
            let odd = ie_sum_pos(d, &p, a, n, m, right);
            let u = union_at(d, &p, a, n);
            let cu = d.const_app(p.count_range, &[u, m]);
            let lhs = d.add(cu, even);
            let concl = d.eq(lhs, odd);
            let with_m = d.pi_fv(m_fv, nat, concl);
            let with_n = d.pi_fv(n_fv, nat, with_m);
            d.pi_fv(a_fv, fam, with_n)
        };
        let real = build(&mut d, false);
        let slid = build(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_inclusion_exclusion_pos;
    assert!(
        f.thm_admits_at(name, real),
        "the classical form must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the union's size sits with the EVEN sum, not the odd one"
    );
}

/// The two-set case really is `Nat.countRange_union_add_inter`.
///
/// One statement, offered twice: once with the derived
/// `Nat.Subsets.inclusion_exclusion_two`, once with the pre-existing
/// `Nat.countRange_union_add_inter` applied at `A 0` and `A 1`. Both must be
/// ADMITTED — that is what "recovers the two-set case" means, and it is not
/// something a reader can check by comparing two rendered types. A third offer,
/// at a statement with `A 0` replaced by `A 1` on the right, must be REJECTED.
#[test]
fn the_two_set_case_is_the_existing_lemma_and_a_slid_one_is_not() {
    let mut f = Fixture::new();
    let p = f.p;

    let build_ty = |d: &mut NatDev<'_>, slid: bool| -> ExprId {
        let nat = d.nat_ty();
        let cty = set_ty(d);
        let fam = d.arrow(nat, cty);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let zero = d.zero();
        let one = d.num(1);
        let p0 = d.apply(a, &[zero]);
        let p1 = d.apply(a, &[one]);
        let u = d.const_app(p.set_union, &[p0, p1]);
        let i = d.const_app(p.set_inter, &[p0, p1]);
        let cu = d.const_app(p.count_range, &[u, m]);
        let ci = d.const_app(p.count_range, &[i, m]);
        let c0 = d.const_app(p.count_range, &[p0, m]);
        let c1 = d.const_app(p.count_range, &[p1, m]);
        let lhs = d.add(cu, ci);
        let rhs = if slid { d.add(c1, c1) } else { d.add(c0, c1) };
        let concl = d.eq(lhs, rhs);
        let with_m = d.pi_fv(m_fv, nat, concl);
        d.pi_fv(a_fv, fam, with_m)
    };

    let (real, slid) = {
        let mut d = f.dev();
        let real = build_ty(&mut d, false);
        let slid = build_ty(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_inclusion_exclusion_two;
    assert!(
        f.thm_admits_at(name, real),
        "the derived two-set case must be admitted at its own statement"
    );

    // The SAME statement, proved by the pre-existing two-set lemma.
    let existing = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let cty = set_ty(&mut d);
        let fam = d.arrow(nat, cty);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let zero = d.zero();
        let one = d.num(1);
        let p0 = d.apply(a, &[zero]);
        let p1 = d.apply(a, &[one]);
        let body = d.lemma(p.count_range_union_add_inter, &[p0, p1, m]);
        let with_m = d.lam_fv(m_fv, nat, body);
        d.lam_fv(a_fv, fam, with_m)
    };
    assert!(
        f.admits(real, existing),
        "Nat.countRange_union_add_inter must prove the derived statement verbatim"
    );

    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the statement with `A 0` replaced by `A 1` must be REJECTED"
    );
}

/// `prodPar_even` puts the residue on the ODD side, and the same proof term is
/// REJECTED with it moved to the even one.
#[test]
fn prod_par_even_is_admitted_and_the_moved_residue_is_not() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let cty = set_ty(&mut d);
        let build = |d: &mut NatDev<'_>, moved: bool| -> ExprId {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let tv = d.bool_true();
            let fal = d.bool_false();
            let even = prod_par(d, &p, c, n, tv);
            let odd = prod_par(d, &p, c, n, fal);
            let residue = none_of(d, &p, c, n);
            let (lhs, rhs) = if moved {
                let padded = d.add(even, residue);
                (padded, odd)
            } else {
                let padded = d.add(odd, residue);
                (even, padded)
            };
            let concl = d.eq(lhs, rhs);
            let with_n = d.pi_fv(n_fv, nat, concl);
            d.pi_fv(c_fv, cty, with_n)
        };
        let real = build(&mut d, false);
        let slid = build(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_prod_par_even;
    assert!(
        f.thm_admits_at(name, real),
        "prodPar_even must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the residue belongs on the ODD side"
    );
}

/// `meetCard_empty` returns the AMBIENT range's size, not the family's width —
/// and the same proof term is REJECTED at the width.
///
/// The two are different `Nat` variables in the same statement, which is
/// exactly the confusion a reader of `meetCard A n empty m` can make.
#[test]
fn meet_card_empty_returns_the_ambient_size_not_the_width() {
    let mut f = Fixture::new();
    let p = f.p;

    let (real, slid) = {
        let mut d = f.dev();
        let nat = d.nat_ty();
        let cty = set_ty(&mut d);
        let fam = d.arrow(nat, cty);
        let build = |d: &mut NatDev<'_>, width: bool| -> ExprId {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let e = empty_set(d, &p);
            let lhs = meet_card(d, &p, a, n, e, m);
            let rhs = if width { n } else { m };
            let concl = d.eq(lhs, rhs);
            let with_m = d.pi_fv(m_fv, nat, concl);
            let with_n = d.pi_fv(n_fv, nat, with_m);
            d.pi_fv(a_fv, fam, with_n)
        };
        let real = build(&mut d, false);
        let slid = build(&mut d, true);
        (real, slid)
    };

    let name = p.subsets_meet_card_empty;
    assert!(
        f.thm_admits_at(name, real),
        "meetCard_empty must be admitted at its own statement"
    );
    assert!(
        !f.thm_admits_at(name, slid),
        "negative control: the answer is the ambient size, not the family width"
    );
}
