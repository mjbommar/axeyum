//! Concrete-instance tests for `list_prelude`'s core operations
//! (`length`/`append`/`map`/`foldr`/`reverse`) and a coverage check that the
//! six pure-`List` theorems landed axiom-free.
//!
//! **The kernel cannot tell a `Definition` is wrong.** Every operation here
//! is admitted on its TYPE alone, and a function computing the wrong value
//! has the right type. So every check reduces a closed term to a numeral or
//! a `nil`/`cons` skeleton with the kernel's own `def_eq` and pairs the
//! positive with the specific wrong formula it rules out. Lists are kept to
//! length ≤ 4 (this prelude's `Nat` numerals are unary `succ` towers).

use super::ops::{apply_all, lam_fvar};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::{BinderInfo, Kernel, ListPrelude, LogicPrelude, build_list_prelude};

struct Fixture {
    k: Kernel,
    p: ListPrelude,
    logic: LogicPrelude,
    zero_lvl: LevelId,
    nat: ExprId,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_list_prelude(&mut k).expect("List prelude must build");
        let logic = crate::build_logic_prelude(&mut k).expect("Logic prelude must build");
        let zero_lvl = k.level_zero();
        let nat = k.const_(logic.nat, vec![]);
        Self {
            k,
            p,
            logic,
            zero_lvl,
            nat,
        }
    }

    fn num(&mut self, n: u32) -> ExprId {
        let mut e = self.k.const_(self.logic.nat_zero, vec![]);
        let succ = self.k.const_(self.logic.nat_succ, vec![]);
        for _ in 0..n {
            e = self.k.app(succ, e);
        }
        e
    }

    fn nil_nat(&mut self) -> ExprId {
        let c = self.k.const_(self.p.nil, vec![self.zero_lvl]);
        self.k.app(c, self.nat)
    }

    fn cons_nat(&mut self, head: ExprId, tail: ExprId) -> ExprId {
        let c = self.k.const_(self.p.cons, vec![self.zero_lvl]);
        let c = self.k.app(c, self.nat);
        let c = self.k.app(c, head);
        self.k.app(c, tail)
    }

    /// `[e0, e1, ..., ek]` as `List Nat`, built right-to-left onto `nil`.
    fn list_of(&mut self, elements: &[u32]) -> ExprId {
        let mut acc = self.nil_nat();
        for &e in elements.iter().rev() {
            let lit = self.num(e);
            acc = self.cons_nat(lit, acc);
        }
        acc
    }

    fn length(&mut self, l: ExprId) -> ExprId {
        let c = self.k.const_(self.p.length, vec![]);
        let c = self.k.app(c, self.nat);
        self.k.app(c, l)
    }

    fn append(&mut self, l1: ExprId, l2: ExprId) -> ExprId {
        let c = self.k.const_(self.p.append, vec![]);
        let c = self.k.app(c, self.nat);
        let c = self.k.app(c, l1);
        self.k.app(c, l2)
    }

    fn reverse(&mut self, l: ExprId) -> ExprId {
        let c = self.k.const_(self.p.reverse, vec![]);
        let c = self.k.app(c, self.nat);
        self.k.app(c, l)
    }

    /// `List.map {Nat} {Nat} Nat.succ l`.
    fn map_succ(&mut self, l: ExprId) -> ExprId {
        let succ = self.k.const_(self.logic.nat_succ, vec![]);
        let c = self.k.const_(self.p.map, vec![]);
        let c = self.k.app(c, self.nat);
        let c = self.k.app(c, self.nat);
        let c = self.k.app(c, succ);
        self.k.app(c, l)
    }

    /// `List.foldr {Nat} {Nat} Nat.add 0 l`, with `add` built inline via
    /// `Nat.rec` (this fixture predates `Nat.add`'s own declaration, exactly
    /// like `List.sum` does in the bridge).
    fn foldr_add(&mut self, l: ExprId) -> ExprId {
        let anon = self.k.anon();
        let a_fv = 99_900;
        let b_fv = 99_901;
        let j_fv = 99_902;
        let ih_fv = 99_903;
        let a = self.k.fvar(a_fv);
        let b = self.k.fvar(b_fv);
        let succ = self.k.const_(self.logic.nat_succ, vec![]);
        let motive = self.k.lam(anon, self.nat, self.nat, BinderInfo::Default);
        // Nat.rec's successor minor premise takes TWO binders, `Π (j : Nat)
        // (ih : motive j), motive (succ j)` — this fixture predates the
        // constant-motive `Nat.rec` helper `nat_prelude::ops::define_binary`
        // uses, so it is rebuilt by hand here, and a first draft of this
        // helper dropped the `j` binder (only `ih`), landing a stuck
        // one-argument closure the recursor rejected as ill-typed at the
        // WRONG position rather than reporting the missing binder.
        let succ_case = {
            let ih = self.k.fvar(ih_fv);
            let succ_ih = self.k.app(succ, ih);
            let inner = lam_fvar(&mut self.k, ih_fv, self.nat, succ_ih, BinderInfo::Default);
            lam_fvar(&mut self.k, j_fv, self.nat, inner, BinderInfo::Default)
        };
        let one = self.k.level_succ(self.zero_lvl);
        let rec = self.k.const_(self.logic.nat_rec, vec![one]);
        let add_ab = apply_all(&mut self.k, rec, &[motive, a, succ_case, b]);
        let add_fn = {
            let with_b = lam_fvar(&mut self.k, b_fv, self.nat, add_ab, BinderInfo::Default);
            lam_fvar(&mut self.k, a_fv, self.nat, with_b, BinderInfo::Default)
        };
        let zero = self.k.const_(self.logic.nat_zero, vec![]);
        let c = self.k.const_(self.p.foldr, vec![]);
        let c = self.k.app(c, self.nat);
        let c = self.k.app(c, self.nat);
        let c = self.k.app(c, add_fn);
        let c = self.k.app(c, zero);
        self.k.app(c, l)
    }
}

#[test]
fn length_is_the_element_count_not_the_predecessor() {
    let mut f = Fixture::new();
    let l = f.list_of(&[1, 2, 3]);
    let len = f.length(l);
    let three = f.num(3);
    let two = f.num(2);
    assert!(f.k.def_eq(len, three), "length [1,2,3] must be 3");
    assert!(
        !f.k.def_eq(len, two),
        "negative control: length [1,2,3] must NOT be 2"
    );

    let empty = f.nil_nat();
    let len0 = f.length(empty);
    let zero = f.num(0);
    assert!(f.k.def_eq(len0, zero), "length [] must be 0");
}

#[test]
fn append_concatenates_in_order() {
    let mut f = Fixture::new();
    let l1 = f.list_of(&[1]);
    let l2 = f.list_of(&[2, 3]);
    let appended = f.append(l1, l2);
    let expected = f.list_of(&[1, 2, 3]);
    let wrong_order = f.list_of(&[2, 3, 1]);
    assert!(
        f.k.def_eq(appended, expected),
        "append [1] [2,3] must be [1,2,3]"
    );
    assert!(
        !f.k.def_eq(appended, wrong_order),
        "negative control: append [1] [2,3] must NOT be [2,3,1]"
    );
}

#[test]
fn reverse_actually_reverses() {
    let mut f = Fixture::new();
    let l = f.list_of(&[1, 2, 3]);
    let reversed = f.reverse(l);
    let expected = f.list_of(&[3, 2, 1]);
    assert!(
        f.k.def_eq(reversed, expected),
        "reverse [1,2,3] must be [3,2,1]"
    );
    assert!(
        !f.k.def_eq(reversed, l),
        "negative control: reverse [1,2,3] must NOT be [1,2,3] (the identity)"
    );
}

#[test]
fn map_applies_pointwise() {
    let mut f = Fixture::new();
    let l = f.list_of(&[0, 1]);
    let mapped = f.map_succ(l);
    let expected = f.list_of(&[1, 2]);
    let wrong = f.list_of(&[0, 1]);
    assert!(f.k.def_eq(mapped, expected), "map succ [0,1] must be [1,2]");
    assert!(
        !f.k.def_eq(mapped, wrong),
        "negative control: map succ [0,1] must NOT be [0,1] (unchanged)"
    );
}

#[test]
fn foldr_add_is_the_sum() {
    let mut f = Fixture::new();
    let l = f.list_of(&[1, 2, 3]);
    let summed = f.foldr_add(l);
    let six = f.num(6);
    let five = f.num(5);
    assert!(f.k.def_eq(summed, six), "foldr add 0 [1,2,3] must be 6");
    assert!(
        !f.k.def_eq(summed, five),
        "negative control: foldr add 0 [1,2,3] must NOT be 5"
    );

    let empty = f.nil_nat();
    let summed0 = f.foldr_add(empty);
    let zero = f.num(0);
    assert!(f.k.def_eq(summed0, zero), "foldr add 0 [] must be 0");
}

/// Coverage: every operation and the six pure-`List` theorems are present,
/// and the whole package declares no axioms — `List` needs no quotient
/// (ADR-1579).
#[test]
fn the_list_prelude_declares_no_axioms() {
    let f = Fixture::new();
    for name in [
        f.p.append_nil,
        f.p.append_assoc,
        f.p.reverse_append,
        f.p.reverse_reverse,
        f.p.length_map,
        f.p.foldr_append,
    ] {
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "expected no axioms for {name:?}, found {footprint:?}"
        );
    }
}
