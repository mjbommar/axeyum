//! Concrete-instance tests for `nat_prelude::avg_pair`'s two definitions.
//!
//! A separate file (rather than an addition to the dense
//! `nat_prelude_tests.rs`) per this session's own merge-hazard note: two
//! lanes editing that one file at once have repeatedly produced a conflict
//! git cuts mid-item. `Fixture` here is a small local copy of
//! `nat_prelude_tests::Fixture` (that one is module-private) — same three
//! fields, same `NatOps` impl, same `build_nat_prelude` call.
//!
//! The kernel cannot tell a `Definition` is wrong — a function of the right
//! TYPE that computes the wrong VALUE is admitted just as happily as a
//! correct one. So every check here is a `def_eq` at concrete numerals
//! against an independently hand-computed value, paired with a negative
//! control naming the specific wrong formula it rules out.

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
}

/// `Nat.avg` computes the FLOORED average, not the ceiling — `Nat.div` and
/// `Nat.sub` both truncate silently, so a rounding-up implementation would
/// still type-check and needs a discriminating test to catch.
///
/// `avg 3 4 = 3` (`7 / 2` floors to `3`; a ceiling implementation would give
/// `4`). `avg 0 1 = 0` is the same boundary at the smallest odd sum (a
/// ceiling implementation would give `1`). `avg 2 7 = 4` (`9 / 2` floors to
/// `4`, ceiling would give `5`) confirms the floor at an unequal, non-unit
/// gap. `avg 5 5 = 5` is the equal-arguments sanity case (`10 / 2 = 5`
/// exactly, no rounding either way to discriminate).
#[test]
fn avg_evaluates_correctly() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let seven = f.num(7);

    let avg_3_4 = f.const_app(p.avg, &[three, four]);
    assert!(f.k.def_eq(avg_3_4, three), "avg 3 4 must floor to 3");
    assert!(
        !f.k.def_eq(avg_3_4, four),
        "negative control: avg 3 4 must NOT round up to 4"
    );

    let avg_0_1 = f.const_app(p.avg, &[zero, one]);
    assert!(f.k.def_eq(avg_0_1, zero), "avg 0 1 must floor to 0");
    assert!(
        !f.k.def_eq(avg_0_1, one),
        "negative control: avg 0 1 must NOT round up to 1"
    );

    let avg_2_7 = f.const_app(p.avg, &[two, seven]);
    assert!(f.k.def_eq(avg_2_7, four), "avg 2 7 must floor to 4");
    assert!(
        !f.k.def_eq(avg_2_7, five),
        "negative control: avg 2 7 must NOT round up to 5"
    );

    let avg_5_5 = f.const_app(p.avg, &[five, five]);
    assert!(f.k.def_eq(avg_5_5, five), "avg 5 5 must be exactly 5");

    for name in [p.avg] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// `Nat.pair` computes the right VALUES at concrete instances, chosen to
/// discriminate against three plausible wrong formulas: the symmetric `a +
/// b`, the textbook two-multiplication Cantor pairing `(a+b)*(a+b+1)/2 +
/// a`, and a transposed branch condition (`b < a` instead of `a < b`).
///
/// Hand-computed table for `a, b` in `[0, 2]` (`pair a b := if a < b then b
/// * b + a else a * a + a + b`):
///
/// | (a,b) | a<b | value |
/// |-------|-----|-------|
/// | (0,0) | no  | 0     |
/// | (0,1) | yes | 1     |
/// | (1,0) | no  | 2     |
/// | (1,1) | no  | 3     |
/// | (0,2) | yes | 4     |
/// | (1,2) | yes | 5     |
/// | (2,0) | no  | 6     |
/// | (2,1) | no  | 7     |
/// | (2,2) | no  | 8     |
///
/// `pair 1 2 = 5` is the discriminating instance: `1 + 2 = 3` (rules out the
/// symmetric-sum formula), the transposed condition `2 < 1` is false so a
/// swapped-branch bug gives `1*1 + 1 + 2 = 4` (rules out a transposed `<`),
/// and the textbook Cantor pairing gives `(3)*(4)/2 + 1 = 7` (rules out that
/// formula — and `7` is not arbitrary: it is exactly `pair 2 1`, so this
/// single check also confirms `pair` is not symmetric, which any injective
/// pairing function over two arguments must not be).
#[test]
fn pair_evaluates_correctly() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let six = f.num(6);
    let seven = f.num(7);
    let eight = f.num(8);

    let pair_0_0 = f.const_app(p.pair, &[zero, zero]);
    assert!(f.k.def_eq(pair_0_0, zero), "pair 0 0 must be 0");

    let pair_0_1 = f.const_app(p.pair, &[zero, one]);
    assert!(f.k.def_eq(pair_0_1, one), "pair 0 1 must be 1");

    let pair_1_0 = f.const_app(p.pair, &[one, zero]);
    assert!(f.k.def_eq(pair_1_0, two), "pair 1 0 must be 2");

    let pair_1_1 = f.const_app(p.pair, &[one, one]);
    assert!(f.k.def_eq(pair_1_1, three), "pair 1 1 must be 3");

    let pair_0_2 = f.const_app(p.pair, &[zero, two]);
    assert!(f.k.def_eq(pair_0_2, four), "pair 0 2 must be 4");

    let pair_1_2 = f.const_app(p.pair, &[one, two]);
    assert!(f.k.def_eq(pair_1_2, five), "pair 1 2 must be 5");
    assert!(
        !f.k.def_eq(pair_1_2, three),
        "negative control: pair 1 2 must NOT be 3 (the symmetric a + b formula)"
    );
    assert!(
        !f.k.def_eq(pair_1_2, four),
        "negative control: pair 1 2 must NOT be 4 (a transposed a<b/b<a branch condition)"
    );
    assert!(
        !f.k.def_eq(pair_1_2, seven),
        "negative control: pair 1 2 must NOT be 7 (the textbook two-multiplication \
         Cantor pairing (a+b)*(a+b+1)/2 + a)"
    );

    let pair_2_0 = f.const_app(p.pair, &[two, zero]);
    assert!(f.k.def_eq(pair_2_0, six), "pair 2 0 must be 6");

    let pair_2_1 = f.const_app(p.pair, &[two, one]);
    assert!(f.k.def_eq(pair_2_1, seven), "pair 2 1 must be 7");
    assert!(
        !f.k.def_eq(pair_2_1, five),
        "negative control: pair 2 1 must NOT equal pair 1 2 (5) -- pair is not symmetric"
    );

    let pair_2_2 = f.const_app(p.pair, &[two, two]);
    assert!(f.k.def_eq(pair_2_2, eight), "pair 2 2 must be 8");

    for name in [p.pair] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}
