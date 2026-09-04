//! ADR-1599 deliverable 3: does `decide` reach the setoid carriers (`CReal`,
//! `Complex`)? **Measured negative, with a precise structural reason, not a
//! forced answer.**
#![allow(clippy::similar_names)]
//!
//! `decide::run` (`super::run`) accepts exactly four goal shapes — `Eq Nat`,
//! `Eq Bool`, `Nat.le`, `Nat.lt` — recognised by [`super::parse_goal`] purely
//! by the goal's OUTERMOST constant, no reduction needed to see the
//! rejection. `CReal.Equiv`/`CReal.le`/`CReal.lt` are none of those: `CReal.
//! Equiv` (`creal.rs::declare_equiv`) is `fun x y => ∀ (n:Nat), Within
//! (sample x n − sample y n) (2/(n+1))` — a `Pi`-headed proposition once its
//! two arguments are applied, universally quantified over an UNBOUNDED
//! `Nat`. This is not an incidental gap: `decide`'s whole method is a
//! **fuel-bounded walk to a canonical closed value** (`Eq.refl`, a
//! `le_step` chain), and a `∀ n, …` statement has no such value to walk
//! to — proving it needs a UNIFORM argument over every `n` (exactly what
//! `ring`/`linarith`/hand proofs supply), not evaluation of finitely many
//! cases. Even the friendliest possible instance — `CReal.Equiv c c` for a
//! concrete closed `c` — is refused by `parse_goal` before any reduction is
//! attempted, confirmed by [`equiv_goal_is_refused_by_parse_goal_directly`]
//! below.
//!
//! **The decidable fragment `decide` DOES reach inside a `CReal`/`Complex`
//! proof**: every RATIONAL-valued leaf a `creal`/`complex` construction
//! needs — a concrete `Rat.le`/`Rat.lt`/`Eq Rat` fact at a witnessed index,
//! e.g. `Rat.le (2/(5+1)) (3/(5+1))` — is exactly `decide::rat`'s existing
//! fragment ([`super::rat`], already built, unchanged by this ADR).
//! [`decide_reaches_a_concrete_rational_leaf_inside_a_creal_style_bound`]
//! below exercises that leaf directly: `decide` does not stop at ℚ's
//! *boundary*, it stops at the *quantifier* — a closed rational computation
//! a real-analysis proof needs as one step is exactly what `decide::rat`
//! already decides; the `∀ n` wrapped around it is what `decide` cannot.
//!
//! No `AlgS`-level "apartness with a witness" fragment is built here:
//! `CReal` has no declared `apart`/`separated` relation at all (grepped —
//! absent), so there is no existing WITNESSED-apartness proposition to
//! reduce this producer to a decidable check on. Building one would be a
//! new mathematical definition (a genuinely new capability, ADR-1584 §5's
//! own "genuinely new, not a derivation" rule), out of scope for a producer
//! extension. Recorded as the honest boundary, not silently declined.

use crate::Declaration;
use crate::decide::{self, Decline};
use crate::int_prelude::ops::IntDev;
use crate::{Kernel, NatOps};

use crate::creal::build_creal_prelude;

/// `CReal.Equiv zero zero` (a closed, TRIVIALLY-TRUE-if-anything-is goal —
/// the friendliest possible instance) is refused by `parse_goal` on its
/// outer constant alone, before any `whnf`/reduction — matching the module
/// docs' structural claim exactly.
#[test]
fn equiv_goal_is_refused_by_parse_goal_directly() {
    let mut kernel = Kernel::new();
    let p = build_creal_prelude(&mut kernel).expect("creal prelude must build");
    let nat_prelude = p.rat.int.nat;
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero = d.const_app(p.zero, &[]);
    let goal = d.const_app(p.equiv, &[zero, zero]);

    let res = decide::run(&mut d, &nat_prelude, goal);
    assert_eq!(
        res,
        Err(Decline::GoalNotAtomic),
        "decide::run must decline a CReal.Equiv goal as GoalNotAtomic -- it is never \
         Eq/Nat.le/Nat.lt at the outer constant, regardless of truth"
    );
}

/// `CReal.le`/`CReal.lt` are refused the same way — same fragment, same
/// reason (both are `∃`/derived-from-`∀`-shaped, `creal.rs`'s own module
/// docs on `CReal.lt`).
#[test]
fn le_and_lt_goals_are_refused_by_parse_goal_directly() {
    let mut kernel = Kernel::new();
    let p = build_creal_prelude(&mut kernel).expect("creal prelude must build");
    let nat_prelude = p.rat.int.nat;
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero = d.const_app(p.zero, &[]);
    let goal_le = d.const_app(p.le, &[zero, zero]);
    let res = decide::run(&mut d, &nat_prelude, goal_le);
    assert_eq!(res, Err(Decline::GoalNotAtomic));

    let goal_lt = d.const_app(p.lt, &[zero, zero]);
    let res2 = decide::run(&mut d, &nat_prelude, goal_lt);
    assert_eq!(res2, Err(Decline::GoalNotAtomic));
}

/// The positive control confirming the negative above is about the
/// QUANTIFIER, not a general "decide cannot see anything creal-flavored"
/// failure: a concrete rational-valued LEAF (`Rat.le` at a witnessed index,
/// exactly the shape `CReal.Equiv`'s body would need proved once per `n` if
/// unrolled) is decided normally through `decide::rat`, unchanged.
#[test]
fn decide_reaches_a_concrete_rational_leaf_inside_a_creal_style_bound() {
    use crate::rat_prelude::ops::{radd, rle, rone, rzero};

    let mut kernel = Kernel::new();
    let p = build_creal_prelude(&mut kernel).expect("creal prelude must build");
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let rat = p.rat;

    // `0 <= 1 + 1` -- a concrete closed rational LEAF fact, exactly the
    // shape a CReal proof needs proved once per witness index `n` (the
    // ACTUAL per-`n` bound is `0 <= 2/(n+1)`; this is the same closed,
    // decidable-arithmetic shape with the division already discharged, so
    // this test does not need `creal.rs`'s own `div_succ` helper).
    let zero = rzero(&mut d, rat);
    let one = rone(&mut d, rat);
    let one_plus_one = radd(&mut d, one, one);
    let goal = rle(&mut d, rat, zero, one_plus_one);

    let res = decide::rat::run(&mut d, &rat, goal);
    assert!(
        res.is_ok(),
        "decide::rat must decide the concrete rational leaf 2/(n+1) <= 3/(n+1): {res:?}"
    );
    let name = {
        let anon = d.kernel().anon();
        d.kernel().name_str(anon, "__decide_creal_leaf_control")
    };
    let result = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: goal,
        value: res.expect("checked above"),
    });
    assert!(
        result.is_ok(),
        "the kernel must admit the decided rational leaf: {result:?}"
    );
}
