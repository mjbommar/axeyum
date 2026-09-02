//! Concrete-instance tests for `nat_prelude::factorization_multiset`.
//!
//! **`Nat.factorizationAux` and `Nat.factorization` are `Definition`s, and the
//! trusted gate cannot tell a `Definition` is wrong** — a trial division that
//! returned the wrong divisor, dropped a repeat, or stopped one step early has
//! exactly the same type. So every check below reduces a closed term to a
//! numeral with the kernel's own `def_eq` and compares it against an
//! independently hand-computed value, with a negative control naming the
//! specific wrong answer it rules out.
//!
//! `12 = 2·2·3` is the discriminating case: it has a repeated factor (so a
//! set-flavoured `add` fails), two distinct primes (so a search that stopped
//! after the first fails), and a composite cofactor at every step. `1` is the
//! boundary the guard `n ≤ 1` exists for, and `7` is the prime case, where the
//! quotient reaches `1` immediately.
//!
//! `factorization 7` is `add (singleton 7) Multiset.zero`, NOT the term
//! `singleton 7` — the recursion always appends the tail — so it is checked
//! through `count` and `card`, which is what "is the multiset `{7}`" actually
//! means here.
//!
//! Every magnitude is tiny on purpose: this prelude's numerals are unary
//! `Nat.succ` towers and cost is superlinear in the largest magnitude FORMED.
//! The largest value any check below builds is `12`.

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

    /// `Nat.factorization n`.
    fn factorization(&mut self, n: u32) -> ExprId {
        let lit = self.num(n);
        let name = self.p.factorization;
        self.const_app(name, &[lit])
    }

    /// `Nat.Multiset.count (factorization n) x`.
    fn count_at(&mut self, m: ExprId, x: u32) -> ExprId {
        let lit = self.num(x);
        let name = self.p.multiset_count;
        self.const_app(name, &[m, lit])
    }

    /// `Nat.Multiset.card m`.
    fn card(&mut self, m: ExprId) -> ExprId {
        let name = self.p.multiset_card;
        self.const_app(name, &[m])
    }

    /// `prime_condition x`, rebuilt here rather than imported
    /// (`nat_prelude::primes::prime_condition` takes a `NatDev`, not a
    /// `Fixture`). Alpha-equivalent to the module's own builder, which is what
    /// makes the `def_eq` comparisons below meaningful.
    fn prime_condition(&mut self, x: ExprId) -> ExprId {
        let nat = self.nat_ty();
        let two = self.num(2);
        let lower = self.le(two, x);
        let c_fv = self.fresh_fvar();
        let c = self.k.fvar(c_fv);
        let divides = self.dvd(c, x);
        let one = self.num(1);
        let trivial = self.eq(c, one);
        let whole = self.eq(c, x);
        let or_name = self.p.logic.or;
        let disjunction = self.const_app(or_name, &[trivial, whole]);
        let body = self.arrow(divides, disjunction);
        let divisors = self.pi_fv(c_fv, nat, body);
        let and_name = self.p.logic.and;
        self.const_app(and_name, &[lower, divisors])
    }

    /// `Le a b` at two literals, via the computational `ble` bridge.
    fn le_lit(&mut self, a: u32, b: u32) -> ExprId {
        let x = self.num(a);
        let y = self.num(b);
        let cond = self.ble(x, y);
        let holds = self.bool_refl(cond);
        let name = self.p.le_of_ble_eq_true;
        self.const_app(name, &[x, y, holds])
    }
}

/// `Nat.factorization 12` is the multiset `{2,2,3}`: the trial division must
/// take `2` twice and then `3`.
///
/// The negative control at `2` is `1`, which is what a `factorization` that
/// divided out each prime only once would give; the control at `3` is `0`,
/// which is what one that stopped after the first factor would give.
#[test]
fn factorization_of_twelve_is_two_two_three() {
    let mut f = Fixture::new();
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);

    let m = f.factorization(12);
    let at_2 = f.count_at(m, 2);
    let at_3 = f.count_at(m, 3);
    let at_5 = f.count_at(m, 5);

    assert!(
        f.k.def_eq(at_2, two),
        "count (factorization 12) 2 must be 2"
    );
    assert!(
        !f.k.def_eq(at_2, one),
        "negative control: count (factorization 12) 2 must NOT be 1 -- that is \
         a factorization that divided each prime out only once"
    );
    assert!(
        f.k.def_eq(at_3, one),
        "count (factorization 12) 3 must be 1"
    );
    assert!(
        !f.k.def_eq(at_3, zero),
        "negative control: count (factorization 12) 3 must NOT be 0 -- that is \
         a search that stopped after the first prime"
    );
    assert!(
        f.k.def_eq(at_5, zero),
        "count (factorization 12) 5 must be 0"
    );

    let size = f.card(m);
    assert!(f.k.def_eq(size, three), "card (factorization 12) must be 3");
    assert!(
        !f.k.def_eq(size, two),
        "negative control: card (factorization 12) must NOT be 2"
    );
}

/// `Nat.factorization 1` is the EMPTY multiset, and `factorization 7` is `{7}`.
///
/// `1` is the boundary the `n ≤ 1` guard exists for: a factorization that
/// recursed there would not terminate at all, and one that emitted
/// `minFac 1 = 1` would put `1` in the multiset, which `count _ 1 = 0` rules
/// out. `7` is the prime case — one step, quotient `1`.
#[test]
fn factorization_handles_one_and_a_prime() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let one = f.num(1);

    let m1 = f.factorization(1);
    let empty = f.k.const_(p.multiset_zero, vec![]);
    assert!(
        f.k.def_eq(m1, empty),
        "factorization 1 must be `Nat.Multiset.zero`"
    );
    let single_one = f.const_app(p.multiset_singleton, &[one]);
    assert!(
        !f.k.def_eq(m1, single_one),
        "negative control: factorization 1 must NOT be `singleton 1` -- \
         `minFac 1 = 1`, so an unguarded recursion would emit it"
    );
    let card1 = f.card(m1);
    assert!(f.k.def_eq(card1, zero), "card (factorization 1) must be 0");

    let m7 = f.factorization(7);
    let at_7 = f.count_at(m7, 7);
    let at_2 = f.count_at(m7, 2);
    let at_3 = f.count_at(m7, 3);
    assert!(f.k.def_eq(at_7, one), "count (factorization 7) 7 must be 1");
    assert!(
        !f.k.def_eq(at_7, zero),
        "negative control: count (factorization 7) 7 must NOT be 0"
    );
    assert!(
        f.k.def_eq(at_2, zero),
        "count (factorization 7) 2 must be 0"
    );
    assert!(
        f.k.def_eq(at_3, zero),
        "count (factorization 7) 3 must be 0"
    );
    let card7 = f.card(m7);
    assert!(f.k.def_eq(card7, one), "card (factorization 7) must be 1");
}

/// `Nat.prod_factorization` INSTANTIATES at `12`, and what it states there is
/// an equation between `12` and `12`.
///
/// The premise `0 < 12` has to be dischargeable for this to say anything, so
/// this also confirms the theorem is not vacuous.
#[test]
fn prod_factorization_instantiates_at_twelve() {
    let mut f = Fixture::new();
    let p = f.p;
    let twelve = f.num(12);
    let six = f.num(6);

    let pos = f.le_lit(1, 12);
    let applied = f.const_app(p.prod_factorization, &[twelve, pos]);
    let ty =
        f.k.infer(applied)
            .expect("prod_factorization must apply at 12");

    let expected = f.eq(twelve, twelve);
    assert!(
        f.k.def_eq(ty, expected),
        "prod_factorization 12 must state `12 = 12` -- i.e. the product of the \
         computed factorization really is 12, got {}",
        f.k.render_lean(ty)
    );
    let wrong = f.eq(six, twelve);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: it must NOT state `6 = 12`"
    );
}

/// `Nat.factorization_prime` INSTANTIATES at `(12, 2)` and concludes primality
/// of `2`.
///
/// The premise `0 < count (factorization 12) 2` is discharged by a proof of
/// `Le 1 2`, which only type-checks because the count really does reduce to
/// `2` — so this ties the theorem to the computed multiset rather than to some
/// abstract one. The negative control is primality of `4`, which is FALSE, so
/// it separates the conclusion from "some proposition about a divisor".
#[test]
fn factorization_prime_instantiates_at_twelve_and_two() {
    let mut f = Fixture::new();
    let p = f.p;
    let twelve = f.num(12);
    let two = f.num(2);
    let four = f.num(4);

    let present = f.le_lit(1, 2);
    let applied = f.const_app(p.factorization_prime, &[twelve, two, present]);
    let ty =
        f.k.infer(applied)
            .expect("factorization_prime must apply at (12, 2)");

    let expected = f.prime_condition(two);
    assert!(
        f.k.def_eq(ty, expected),
        "factorization_prime (12, 2) must conclude primality of 2, got {}",
        f.k.render_lean(ty)
    );
    let wrong = f.prime_condition(four);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: it must NOT conclude primality of 4"
    );
}

/// `Nat.Multiset.prod_singleton` and `Nat.prodRange_eq_one_of_below` state what
/// their names claim, at a value where a wrong fold is visible.
///
/// `prod (singleton 3) = 3` is the check `prod_singleton` exists for: the fold
/// runs over `[0, 4)` and every factor below `3` must collapse to `1`, so a
/// `prod_singleton` proved about a fold that forgot the truncation would give
/// `0` (from the `q = 0` factor) rather than `3`.
#[test]
fn prod_singleton_evaluates() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let three = f.num(3);

    let single = f.const_app(p.multiset_singleton, &[three]);
    let folded = f.const_app(p.multiset_prod, &[single]);
    assert!(f.k.def_eq(folded, three), "prod (singleton 3) must be 3");
    assert!(
        !f.k.def_eq(folded, zero),
        "negative control: prod (singleton 3) must NOT be 0 -- that is the \
         value a fold whose `q = 0` factor was not `0 ^ 0 = 1` would give"
    );

    let applied = f.const_app(p.multiset_prod_singleton, &[three]);
    let ty = f.k.infer(applied).expect("prod_singleton must instantiate");
    let expected = f.eq(three, three);
    assert!(
        f.k.def_eq(ty, expected),
        "prod_singleton 3 must state `3 = 3`, got {}",
        f.k.render_lean(ty)
    );
    let wrong = f.eq(zero, three);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: it must NOT state `0 = 3`"
    );
}
