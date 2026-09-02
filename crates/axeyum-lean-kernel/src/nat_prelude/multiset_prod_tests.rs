//! Concrete-instance tests for `nat_prelude::multiset_prod`.
//!
//! `Nat.Multiset.prod_add` is a THEOREM, so the kernel really did check it —
//! but it is a theorem about `Nat.Multiset.prod`, and `prod` is a
//! `Definition`, which the trusted gate cannot tell is wrong. So the checks
//! below do two separate jobs:
//!
//! 1. **Evaluate.** `prod {2,2,3} = 12`, `prod {3} = 3`, and
//!    `prod (add {2,2,3} {3}) = 36`, each reduced to a numeral by the kernel's
//!    own `def_eq` and compared against a hand-computed value, each paired with
//!    the specific wrong value it rules out.
//! 2. **Instantiate.** `prod_add` applied at that same pair must INFER to
//!    `Eq 36 36` — which is the evaluation and the theorem tied together, and
//!    is what a `prod_add` proved about some other fold would fail.
//!
//! `{2,2,3}` and `{3}` are the pair the lane brief names, and they discriminate:
//! `12 · 3 = 36` distinguishes a genuine product from a `prod` that dropped the
//! repeated `2` (which would give `6 · 3 = 18`) and from one that folded the two
//! bounds together without collapsing either tail.
//!
//! Every magnitude here is tiny on purpose: this prelude's numerals are unary
//! `Nat.succ` towers, so cost is superlinear in the largest magnitude FORMED.
//! The largest value any check below builds is `48`.

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

    /// The multiset with the given elements, added left to right.
    fn of(&mut self, elements: &[u32]) -> ExprId {
        let (first, rest) = elements.split_first().expect("at least one element");
        let mut acc = self.singleton(*first);
        for &e in rest {
            let s = self.singleton(e);
            acc = self.union(acc, s);
        }
        acc
    }

    /// `Nat.Multiset.prod m`.
    fn prod(&mut self, m: ExprId) -> ExprId {
        let name = self.p.multiset_prod;
        self.const_app(name, &[m])
    }
}

/// `Nat.Multiset.prod` computes the product with multiplicity, and the two
/// summands of the worked pair evaluate to `12` and `3`.
///
/// The negative control that matters is `6`: that is what `prod {2,2,3}` would
/// be if `count` (or `add`) discarded the repeated `2`, and every check in
/// `multiset_tests.rs` about `count` alone would still pass.
#[test]
fn prod_evaluates_the_worked_pair() {
    let mut f = Fixture::new();
    let twelve = f.num(12);
    let six = f.num(6);
    let three = f.num(3);
    let thirty_six = f.num(36);

    let m = f.of(&[2, 2, 3]);
    let prod_m = f.prod(m);
    assert!(f.k.def_eq(prod_m, twelve), "prod {{2,2,3}} must be 12");
    assert!(
        !f.k.def_eq(prod_m, six),
        "negative control: prod {{2,2,3}} must NOT be 6 -- that is the value a \
         `prod` which discarded the repeated 2 would give"
    );

    let s3 = f.singleton(3);
    let prod_s3 = f.prod(s3);
    assert!(f.k.def_eq(prod_s3, three), "prod {{3}} must be 3");

    let joined = f.union(m, s3);
    let prod_joined = f.prod(joined);
    assert!(
        f.k.def_eq(prod_joined, thirty_six),
        "prod (add {{2,2,3}} {{3}}) must be 36"
    );
    assert!(
        !f.k.def_eq(prod_joined, twelve),
        "negative control: prod (add {{2,2,3}} {{3}}) must NOT be 12 -- that is \
         what a `prod` blind to the right summand would give"
    );
}

/// `Nat.Multiset.prod_add` INSTANTIATES at the worked pair, and what it states
/// there is `36 = 12 · 3`.
///
/// This is the check that ties the theorem to the numbers: `prod_add` proved
/// about a differently-folded product would still type-check as a theorem, and
/// would still be admitted, but would not infer to an equation between these
/// values.
#[test]
fn prod_add_instantiates_to_thirty_six() {
    let mut f = Fixture::new();
    let p = f.p;
    let m = f.of(&[2, 2, 3]);
    let s3 = f.singleton(3);

    let applied = f.const_app(p.multiset_prod_add, &[m, s3]);
    let ty =
        f.k.infer(applied)
            .expect("prod_add must instantiate at ({2,2,3}, {3})");

    let twelve = f.num(12);
    let three = f.num(3);
    let thirty_six = f.num(36);
    let product = f.mul(twelve, three);
    let expected = f.eq(thirty_six, product);
    assert!(
        f.k.def_eq(ty, expected),
        "prod_add ({{2,2,3}}, {{3}}) must state `36 = 12 * 3`, got {}",
        f.k.render_lean(ty)
    );

    let wrong = f.eq(twelve, product);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: it must NOT state `12 = 12 * 3`"
    );
}

/// `Nat.prodRange_mul` INSTANTIATES at two concrete functions whose folds are
/// different numbers.
///
/// `f i = i + 1` over `[0,3)` folds to `1·2·3 = 6`; `g i = 2` folds to `8`; the
/// pointwise product folds to `2·4·6 = 48`. The two factors are deliberately
/// unequal, so a `prodRange_mul` that squared one side or dropped the other
/// gives a different number.
#[test]
fn prod_range_mul_instantiates_at_two_unequal_folds() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let succ_fn = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let body = f.succ(i);
        f.lam_fv(i_fv, nat, body)
    };
    let two_fn = {
        let i_fv = f.fresh_fvar();
        let two = f.num(2);
        f.lam_fv(i_fv, nat, two)
    };
    let three = f.num(3);

    let applied = f.const_app(p.prod_range_mul, &[succ_fn, two_fn, three]);
    let ty =
        f.k.infer(applied)
            .expect("prodRange_mul must instantiate at two concrete functions");

    let forty_eight = f.num(48);
    let six = f.num(6);
    let eight = f.num(8);
    let product = f.mul(six, eight);
    let expected = f.eq(forty_eight, product);
    assert!(
        f.k.def_eq(ty, expected),
        "prodRange_mul (succ, const 2, 3) must state `48 = 6 * 8`, got {}",
        f.k.render_lean(ty)
    );

    let squared = f.mul(six, six);
    let wrong = f.eq(forty_eight, squared);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: it must NOT state `48 = 6 * 6`"
    );
}
