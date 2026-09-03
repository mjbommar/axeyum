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
//! correct one. So every check here is a concrete-numeral evaluation
//! against an independently hand-computed value, paired with a negative
//! control naming the specific wrong formula it rules out. Ten of the
//! positive checks (`ADR-1589`) are routed through `crate::decide` rather
//! than asserted as a bare `Kernel::def_eq` boolean: the assertion becomes
//! "the fourth producer emits a term the KERNEL accepts a declaration for",
//! not "a boolean came back `true`" — the trust anchor, not `def_eq`'s
//! opinion of itself. The negative controls stay as direct `def_eq` checks:
//! `decide` PROVES a goal or declines, it has no "prove this is false" mode,
//! so a negative control is not something it can retire.

use crate::{ExprId, Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

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

/// Retire a hand-written `def_eq` evaluation check onto `crate::decide`:
/// build `Eq lhs rhs`, require `decide::run` to close it, and require the
/// KERNEL to accept a fresh `theorem <tag> : Eq lhs rhs` declaration built
/// from the emitted term. `tag` must be unique within the calling test (it
/// names the declaration).
fn assert_decide(f: &mut Fixture, tag: &str, lhs: ExprId, rhs: ExprId) {
    let p = f.p;
    let goal = f.eq(lhs, rhs);
    let term = crate::decide::run(f, &p, goal).unwrap_or_else(|e| panic!("{tag}: declined: {e:?}"));
    let root = f.k.anon();
    let name = f.k.name_str(root, tag);
    f.declare_theorem(name, goal, term)
        .unwrap_or_else(|e| panic!("{tag}: kernel rejected the emitted term: {e:?}"));
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
    assert_decide(&mut f, "avg_3_4_floors_to_3", avg_3_4, three);
    assert!(
        !f.k.def_eq(avg_3_4, four),
        "negative control: avg 3 4 must NOT round up to 4"
    );

    let avg_0_1 = f.const_app(p.avg, &[zero, one]);
    assert_decide(&mut f, "avg_0_1_floors_to_0", avg_0_1, zero);
    assert!(
        !f.k.def_eq(avg_0_1, one),
        "negative control: avg 0 1 must NOT round up to 1"
    );

    let avg_2_7 = f.const_app(p.avg, &[two, seven]);
    assert_decide(&mut f, "avg_2_7_floors_to_4", avg_2_7, four);
    assert!(
        !f.k.def_eq(avg_2_7, five),
        "negative control: avg 2 7 must NOT round up to 5"
    );

    let avg_5_5 = f.const_app(p.avg, &[five, five]);
    assert_decide(&mut f, "avg_5_5_is_5", avg_5_5, five);

    let name = p.avg;
    assert!(
        f.k.axiom_footprint(name).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(name)
    );
}

/// `Nat.pair` computes the right VALUES at concrete instances, chosen to
/// discriminate against three plausible wrong formulas: the symmetric `a +
/// b`, the textbook two-multiplication Cantor pairing `(a+b)*(a+b+1)/2 +
/// a`, and a transposed branch condition (`b < a` instead of `a < b`).
///
/// Hand-computed table for `a, b` in `[0, 2]`
/// (`pair a b := if a < b then b * b + a else a * a + a + b`):
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

    let pair_0_0 = f.const_app(p.pair_fn, &[zero, zero]);
    assert_decide(&mut f, "pair_0_0_is_0", pair_0_0, zero);

    let pair_0_1 = f.const_app(p.pair_fn, &[zero, one]);
    assert_decide(&mut f, "pair_0_1_is_1", pair_0_1, one);

    let pair_1_0 = f.const_app(p.pair_fn, &[one, zero]);
    assert_decide(&mut f, "pair_1_0_is_2", pair_1_0, two);

    let pair_1_1 = f.const_app(p.pair_fn, &[one, one]);
    assert_decide(&mut f, "pair_1_1_is_3", pair_1_1, three);

    let pair_0_2 = f.const_app(p.pair_fn, &[zero, two]);
    assert_decide(&mut f, "pair_0_2_is_4", pair_0_2, four);

    let pair_1_2 = f.const_app(p.pair_fn, &[one, two]);
    assert_decide(&mut f, "pair_1_2_is_5", pair_1_2, five);
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

    let pair_2_0 = f.const_app(p.pair_fn, &[two, zero]);
    assert!(f.k.def_eq(pair_2_0, six), "pair 2 0 must be 6");

    let pair_2_1 = f.const_app(p.pair_fn, &[two, one]);
    assert!(f.k.def_eq(pair_2_1, seven), "pair 2 1 must be 7");
    assert!(
        !f.k.def_eq(pair_2_1, five),
        "negative control: pair 2 1 must NOT equal pair 1 2 (5) -- pair is not symmetric"
    );

    let pair_2_2 = f.const_app(p.pair_fn, &[two, two]);
    assert!(f.k.def_eq(pair_2_2, eight), "pair 2 2 must be 8");

    let name = p.pair_fn;
    assert!(
        f.k.axiom_footprint(name).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(name)
    );
}
