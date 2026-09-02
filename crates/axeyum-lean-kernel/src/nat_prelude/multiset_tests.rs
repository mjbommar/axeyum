//! Concrete-instance tests for `nat_prelude::multiset`.
//!
//! A separate file (rather than an addition to the dense
//! `nat_prelude_tests.rs`) per this development's merge-hazard note: two lanes
//! editing that one file at once have repeatedly produced a conflict git cuts
//! mid-item. `Fixture` here is a small local copy of
//! `nat_prelude_tests::Fixture` (that one is module-private).
//!
//! **The kernel cannot tell a `Definition` is wrong.** `Nat.Multiset.count`,
//! `add`, `prod`, `card` and `beq` are all admitted on their TYPE, and a
//! function that computes the wrong value has the right type. So every check
//! here reduces a closed term to a numeral with the kernel's own `def_eq` and
//! compares it against an independently hand-computed value, and every positive
//! is paired with the specific wrong formula it rules out.
//!
//! Every magnitude here is tiny on purpose: this prelude's numerals are unary
//! `Nat.succ` towers, so cost is superlinear in the largest magnitude FORMED.
//! The largest value any test below builds is `24` (a negative control), and
//! the largest bound any fold runs over is `18`.

use crate::expr::ExprId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
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
        Self { k, p, st }
    }

    /// `Nat.Multiset.singleton a`.
    fn singleton(&mut self, a: u32) -> ExprId {
        let lit = self.num(a);
        let name = self.p.multiset_singleton;
        self.const_app(name, &[lit])
    }

    /// `Nat.Multiset.add m1 m2`.
    fn union(&mut self, m1: ExprId, m2: ExprId) -> ExprId {
        let name = self.p.multiset_add;
        self.const_app(name, &[m1, m2])
    }

    /// The multiset with the given elements, added left to right. Panics on an
    /// empty list — use `Nat.Multiset.zero` directly for that.
    fn of(&mut self, elements: &[u32]) -> ExprId {
        let (first, rest) = elements.split_first().expect("at least one element");
        let mut acc = self.singleton(*first);
        for &e in rest {
            let s = self.singleton(e);
            acc = self.union(acc, s);
        }
        acc
    }

    /// `Nat.Multiset.count m x`.
    fn count(&mut self, m: ExprId, x: u32) -> ExprId {
        let lit = self.num(x);
        let name = self.p.multiset_count;
        self.const_app(name, &[m, lit])
    }
}

/// `Nat.Multiset.count` reads the multiplicity, and **truncates at the bound**.
///
/// `singleton 2` stores `fun q => if q == 2 then 1 else 0` with bound `3`, so
/// `count` must be `1` at `2` and `0` everywhere else — including at `5`, which
/// is above the bound and therefore reached through the truncation branch
/// rather than through `beq`. The two zeros are not redundant: `3` exercises
/// `beq q 2 = false` below the bound, `5` exercises `ble 6 3 = false` above it,
/// and a `count` that forgot the truncation would still pass at `3`.
#[test]
fn count_reads_a_singleton_and_truncates_at_the_bound() {
    let mut f = Fixture::new();
    let zero = f.zero();
    let one = f.num(1);

    let s2 = f.singleton(2);
    let at_2 = f.count(s2, 2);
    let at_3 = f.count(s2, 3);
    let at_5 = f.count(s2, 5);

    assert!(f.k.def_eq(at_2, one), "count (singleton 2) 2 must be 1");
    assert!(
        !f.k.def_eq(at_2, zero),
        "negative control: count (singleton 2) 2 must NOT be 0"
    );
    assert!(f.k.def_eq(at_3, zero), "count (singleton 2) 3 must be 0");
    assert!(
        !f.k.def_eq(at_3, one),
        "negative control: count (singleton 2) 3 must NOT be 1"
    );
    assert!(
        f.k.def_eq(at_5, zero),
        "count (singleton 2) 5 must be 0 -- above the bound"
    );
    assert!(
        !f.k.def_eq(at_5, one),
        "negative control: count (singleton 2) 5 must NOT be 1"
    );
}

/// `Nat.Multiset.add` adds multiplicities pointwise, and repeated elements
/// accumulate.
///
/// `{2,2,3}` has `count _ 2 = 2` — the case a set-flavoured `add` (max, or
/// "already present, leave it") would get wrong while still passing every
/// singleton check above. `count (add {2,2,3} {3}) 3 = 2` is the brief's own
/// case and the one that exercises `add` on a left argument that is itself a
/// sum, so a bound computed only from the outermost `mk` would be caught.
#[test]
fn add_accumulates_multiplicities() {
    let mut f = Fixture::new();
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);

    let m = f.of(&[2, 2, 3]);
    let at_0 = f.count(m, 0);
    let at_1 = f.count(m, 1);
    let at_2 = f.count(m, 2);
    let at_3 = f.count(m, 3);
    assert!(f.k.def_eq(at_0, zero), "count {{2,2,3}} 0 must be 0");
    assert!(f.k.def_eq(at_1, zero), "count {{2,2,3}} 1 must be 0");
    assert!(f.k.def_eq(at_2, two), "count {{2,2,3}} 2 must be 2");
    assert!(
        !f.k.def_eq(at_2, one),
        "negative control: count {{2,2,3}} 2 must NOT be 1 -- a set-flavoured \
         `add` that discards the repeat"
    );
    assert!(f.k.def_eq(at_3, one), "count {{2,2,3}} 3 must be 1");

    let s3 = f.singleton(3);
    let joined = f.union(m, s3);
    let joined_at_3 = f.count(joined, 3);
    assert!(
        f.k.def_eq(joined_at_3, two),
        "count (add {{2,2,3}} {{3}}) 3 must be 2"
    );
    assert!(
        !f.k.def_eq(joined_at_3, one),
        "negative control: count (add {{2,2,3}} {{3}}) 3 must NOT be 1"
    );
    let joined_at_2 = f.count(joined, 2);
    assert!(
        f.k.def_eq(joined_at_2, two),
        "count (add {{2,2,3}} {{3}}) 2 must still be 2"
    );
    // `count` above the bound of the LEFT summand but below the sum's own
    // bound: `{2,2,3}` has bound 10, `add {2,2,3} {3}` has bound 14, and 11 is
    // between them. Truncation must still give 0 rather than reading `raw`.
    let joined_at_11 = f.count(joined, 11);
    assert!(
        f.k.def_eq(joined_at_11, zero),
        "count (add {{2,2,3}} {{3}}) 11 must be 0"
    );
}

/// `Nat.Multiset.prod` and `Nat.Multiset.card`.
///
/// `prod {2,2,3} = 2^2 * 3 = 12`, and the two negative controls name the two
/// ways to get it wrong that a type check cannot see: `6` is the product of the
/// DISTINCT elements (multiplicity dropped), `24` is `2^2 * 3 * 2` (an element
/// counted once too often). `card {2,2,3} = 3` counts with multiplicity, and
/// `2` is the same set-flavoured error on the sum side.
///
/// `prod zero = 1` is the empty product, and it is the case that would break if
/// `prod` folded with `0` as the unit.
#[test]
fn prod_and_card_evaluate_with_multiplicity() {
    let mut f = Fixture::new();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let six = f.num(6);
    let twelve = f.num(12);
    let twenty_four = f.num(24);

    let m = f.of(&[2, 2, 3]);
    let prod_name = f.p.multiset_prod;
    let card_name = f.p.multiset_card;
    let prod_m = f.const_app(prod_name, &[m]);
    let card_m = f.const_app(card_name, &[m]);

    assert!(f.k.def_eq(prod_m, twelve), "prod {{2,2,3}} must be 12");
    assert!(
        !f.k.def_eq(prod_m, six),
        "negative control: prod {{2,2,3}} must NOT be 6 -- multiplicity dropped"
    );
    assert!(
        !f.k.def_eq(prod_m, twenty_four),
        "negative control: prod {{2,2,3}} must NOT be 24 -- an element counted twice"
    );
    assert!(f.k.def_eq(card_m, three), "card {{2,2,3}} must be 3");
    assert!(
        !f.k.def_eq(card_m, two),
        "negative control: card {{2,2,3}} must NOT be 2"
    );

    let zero_ms = {
        let name = f.p.multiset_zero;
        f.k.const_(name, vec![])
    };
    let prod_zero = f.const_app(prod_name, &[zero_ms]);
    let card_zero = f.const_app(card_name, &[zero_ms]);
    let zero = f.zero();
    assert!(f.k.def_eq(prod_zero, one), "prod zero must be the unit 1");
    assert!(
        !f.k.def_eq(prod_zero, zero),
        "negative control: prod zero must NOT be 0"
    );
    assert!(f.k.def_eq(card_zero, zero), "card zero must be 0");
}

/// `Nat.Multiset.beq` compares multiplicities below the bound, so it is blind
/// to the order the elements were added in and sees a repeated element.
///
/// `beq {2,3} {3,2} = true` is the whole point of a multiset: the two are built
/// by `add` in opposite orders, with different `raw` functions and different
/// `mk` arguments, and are still equal. `beq {2,3} {2,3,3} = false` is the
/// discriminating negative — a comparison that only checked the SUPPORT would
/// return `true` there.
#[test]
fn beq_is_order_blind_and_multiplicity_sensitive() {
    let mut f = Fixture::new();
    let true_val = f.bool_true();
    let false_val = f.bool_false();
    let beq_name = f.p.multiset_beq;

    let m23 = f.of(&[2, 3]);
    let m32 = f.of(&[3, 2]);
    let m233 = f.of(&[2, 3, 3]);

    let swapped = f.const_app(beq_name, &[m23, m32]);
    assert!(
        f.k.def_eq(swapped, true_val),
        "beq {{2,3}} {{3,2}} must be true -- a multiset has no order"
    );
    assert!(
        !f.k.def_eq(swapped, false_val),
        "negative control: beq {{2,3}} {{3,2}} must NOT be false"
    );

    let extra = f.const_app(beq_name, &[m23, m233]);
    assert!(
        f.k.def_eq(extra, false_val),
        "beq {{2,3}} {{2,3,3}} must be false -- multiplicity differs at 3"
    );
    assert!(
        !f.k.def_eq(extra, true_val),
        "negative control: beq {{2,3}} {{2,3,3}} must NOT be true -- a \
         support-only comparison would return true here"
    );

    let self_eq = f.const_app(beq_name, &[m233, m233]);
    assert!(
        f.k.def_eq(self_eq, true_val),
        "beq {{2,3,3}} {{2,3,3}} must be true"
    );
}

/// `Nat.Multiset.raw` is NOT `count`: it reads the stored function without
/// truncating, and a `count` that forgot the truncation would be `def_eq` to it
/// everywhere.
///
/// `mk (fun _ => 1) 2` stores the constant `1` with bound `2`. `raw` gives `1`
/// at every argument; `count` gives `1` below `2` and `0` at or above it. The
/// test asserts both, so a `count` defined as `raw` fails and a `raw` defined as
/// `count` fails too.
#[test]
fn raw_and_count_disagree_above_the_bound() {
    let mut f = Fixture::new();
    let nat = f.nat_ty();
    let zero = f.zero();
    let one = f.num(1);

    let const_one = {
        let q_fv = f.fresh_fvar();
        let body = f.num(1);
        f.lam_fv(q_fv, nat, body)
    };
    let two = f.num(2);
    let mk = f.p.multiset_mk;
    let m = f.const_app(mk, &[const_one, two]);

    let raw_name = f.p.multiset_raw;
    let seven = f.num(7);
    let raw_at_7 = f.const_app(raw_name, &[m, seven]);
    assert!(
        f.k.def_eq(raw_at_7, one),
        "raw (mk (fun _ => 1) 2) 7 must be 1 -- raw does not truncate"
    );

    let count_at_1 = f.count(m, 1);
    let count_at_7 = f.count(m, 7);
    assert!(
        f.k.def_eq(count_at_1, one),
        "count (mk (fun _ => 1) 2) 1 must be 1 -- below the bound"
    );
    assert!(
        f.k.def_eq(count_at_7, zero),
        "count (mk (fun _ => 1) 2) 7 must be 0 -- at or above the bound"
    );
    assert!(
        !f.k.def_eq(count_at_7, one),
        "negative control: `count` must NOT be `raw` -- it truncates"
    );
}
