//! Concrete-instance tests for `nat_prelude::minmax`'s four definitions.
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
//! control naming the specific wrong formula it rules out (in particular,
//! a swapped branch that always returns the SAME argument regardless of
//! which is larger).

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

/// `Max.max` computes the LARGER of its two arguments at both orderings —
/// `max 2 7` takes the `a <= b` branch (`b`) and `max 7 2` takes the other
/// (`a`), so checking both confirms the branch selection is right in
/// general, not merely correct for one argument order by coincidence
/// (a formula that always returns the SAME position, e.g. always `b`,
/// would pass `max 2 7 = 7` and fail `max 7 2 = 7`). `max 5 5 = 5` is the
/// `a == b` boundary, where `Nat.ble a b` is `true` and either branch
/// happens to agree.
#[test]
fn max_evaluates_correctly() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let five = f.num(5);
    let seven = f.num(7);

    let max_2_7 = f.const_app(p.max_max, &[two, seven]);
    assert!(f.k.def_eq(max_2_7, seven), "max 2 7 must be 7");
    assert!(
        !f.k.def_eq(max_2_7, two),
        "negative control: max 2 7 must NOT be 2 (a swapped branch)"
    );

    let max_7_2 = f.const_app(p.max_max, &[seven, two]);
    assert!(f.k.def_eq(max_7_2, seven), "max 7 2 must be 7");
    assert!(
        !f.k.def_eq(max_7_2, two),
        "negative control: max 7 2 must NOT be 2 (a formula that always returns b)"
    );

    let max_5_5 = f.const_app(p.max_max, &[five, five]);
    assert!(f.k.def_eq(max_5_5, five), "max 5 5 must be exactly 5");

    let name = p.max_max;
    assert!(
        f.k.axiom_footprint(name).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(name)
    );
}

/// `Min.min` computes the SMALLER of its two arguments at both orderings,
/// same discrimination logic as [`max_evaluates_correctly`]: `min 2 7`
/// takes the `a <= b` branch (`a`), `min 7 2` takes the other (`b`), and a
/// formula that always returns one fixed position would pass one of these
/// and fail the other.
#[test]
fn min_evaluates_correctly() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let five = f.num(5);
    let seven = f.num(7);

    let min_2_7 = f.const_app(p.min_min, &[two, seven]);
    assert!(f.k.def_eq(min_2_7, two), "min 2 7 must be 2");
    assert!(
        !f.k.def_eq(min_2_7, seven),
        "negative control: min 2 7 must NOT be 7 (a formula that always returns b)"
    );

    let min_7_2 = f.const_app(p.min_min, &[seven, two]);
    assert!(f.k.def_eq(min_7_2, two), "min 7 2 must be 2");
    assert!(
        !f.k.def_eq(min_7_2, seven),
        "negative control: min 7 2 must NOT be 7 (a swapped branch)"
    );

    let min_5_5 = f.const_app(p.min_min, &[five, five]);
    assert!(f.k.def_eq(min_5_5, five), "min 5 5 must be exactly 5");

    let name = p.min_min;
    assert!(
        f.k.axiom_footprint(name).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(name)
    );
}

/// `Nat.instMax`/`instMinNat` compute the SAME values as `Max.max`/
/// `Min.min` (they are same-value aliases under the name Mathlib's
/// elaborated statements apply as the instance argument — see
/// `minmax.rs`'s module doc for why they are not real typeclass
/// instances). Checked two ways: concrete-instance agreement, and that
/// `Nat.instMax a b` is `def_eq` to `Max.max a b` at genuinely free
/// variables (not merely at the numerals already checked above), which a
/// hand-miscopied alias would fail even if every concrete instance by
/// coincidence agreed.
#[test]
fn inst_aliases_agree_with_max_min() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let seven = f.num(7);

    let inst_max_2_7 = f.const_app(p.nat_inst_max, &[two, seven]);
    assert!(f.k.def_eq(inst_max_2_7, seven), "Nat.instMax 2 7 must be 7");
    assert!(
        !f.k.def_eq(inst_max_2_7, two),
        "negative control: Nat.instMax 2 7 must NOT be 2"
    );

    let inst_min_2_7 = f.const_app(p.inst_min_nat, &[two, seven]);
    assert!(f.k.def_eq(inst_min_2_7, two), "instMinNat 2 7 must be 2");
    assert!(
        !f.k.def_eq(inst_min_2_7, seven),
        "negative control: instMinNat 2 7 must NOT be 7"
    );

    // Symbolic agreement: at genuinely free fvars, not numerals that could
    // coincidentally reduce to the same normal form both ways.
    let x_fv = f.fresh_fvar();
    let x = f.k.fvar(x_fv);
    let y_fv = f.fresh_fvar();
    let y = f.k.fvar(y_fv);

    let inst_max_xy = f.const_app(p.nat_inst_max, &[x, y]);
    let max_xy = f.const_app(p.max_max, &[x, y]);
    assert!(
        f.k.def_eq(inst_max_xy, max_xy),
        "Nat.instMax must be def_eq to Max.max at free variables"
    );

    let inst_min_xy = f.const_app(p.inst_min_nat, &[x, y]);
    let min_xy = f.const_app(p.min_min, &[x, y]);
    assert!(
        f.k.def_eq(inst_min_xy, min_xy),
        "instMinNat must be def_eq to Min.min at free variables"
    );

    for name in [p.nat_inst_max, p.inst_min_nat] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}
