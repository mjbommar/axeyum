//! Tests for the ℚ `Tactic` combinator.
//!
//! No `Then(Simp, _)` battery here — [`super`]'s own module docs: there is
//! no `simp::rat`, so `Tactic::Then` for this carrier is ALWAYS the
//! sequential-fallback regime (try the first, and on decline try the
//! second on the SAME goal), never a normalize-then-glue composition, and
//! there is no `glue_rel` to corrupt the way `tactic::int::tests`'s own
//! corrupted-glue test does.
//!
//! Three batteries:
//!
//! 1. **Three `Then` goals that neither producer alone closes** —
//!    `ring::rat::prove` declines OUTRIGHT on any non-`Eq` goal shape
//!    (`Rat.le`/`Rat.lt`) and `decide::rat::run` declines `NotClosed` on
//!    any goal with a free variable, so `Then(Ring, Linarith)`/
//!    `Then(Decide, Linarith)` genuinely need the fallback: the FIRST
//!    tactic is disqualified by the goal's own shape, not merely
//!    "weaker", and `linarith::generic` is what actually closes it.
//! 2. **`First([Decide, Ring, Linarith])`** on a mix, aggregating declines
//!    when none apply.
//! 3. **A mismatched producer output is rejected by the KERNEL** — the
//!    closest analogue to a "corrupted glue" test this carrier has: a
//!    genuine `ring::rat` proof of one `Eq Rat` goal, spliced in as if it
//!    proved a DIFFERENT one.

#![allow(clippy::many_single_char_names)]

use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::idx::ordered_ring::{ADD, LE, ZERO};
use crate::nat_prelude::structures::sel;
use crate::rat_prelude::ops::req;
use crate::ring;
use crate::tactic::rat::{self, Ctx, Decline, Tactic};
use crate::{Kernel, NameId, RatPrelude, build_rat_prelude, on_a_deep_stack};

/// `Rat.orderedRing : Alg.OrderedRing` — the SAME instance term
/// `linarith::generic::Problem::new` derives its own `le`/`add`/… selectors
/// from, so a goal built with these helpers matches what the producer
/// itself re-derives.
fn ring_term(d: &mut IntDev<'_>, p: &RatPrelude) -> ExprId {
    let name = p.algebra_ext.rat_ordered_ring;
    d.kernel().const_(name, vec![])
}

/// The binary relation/operation at field index `idx` of `Alg.OrderedRing`
/// (`ordered_ring::{LE, ADD, …}`), applied to `a`, `b` — NOT `Rat.le`/
/// `Rat.add` directly (a different, if defeq, term): `linarith::generic`
/// parses goals structurally against the SELECTOR application it builds
/// internally, not against the specialized `Rat`-level definition.
fn generic_rel(d: &mut IntDev<'_>, p: &RatPrelude, idx: usize, a: ExprId, b: ExprId) -> ExprId {
    let ring = ring_term(d, p);
    let rn = p.int.nat.structures.ordered_ring;
    let rel = sel(d.kernel(), &rn, idx, ring);
    d.apply(rel, &[a, b])
}

/// The `Alg.OrderedRing` instance's own `zero` field — NOT `Rat.zero`
/// directly, for the same reason [`generic_rel`] avoids `Rat.le`/`Rat.add`.
fn generic_zero(d: &mut IntDev<'_>, p: &RatPrelude) -> ExprId {
    let ring = ring_term(d, p);
    let rn = p.int.nat.structures.ordered_ring;
    sel(d.kernel(), &rn, ZERO, ring)
}

struct Fixture {
    k: Kernel,
    p: RatPrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("Rat prelude must build");
        Self { k, p }
    }

    fn dev(&mut self) -> IntDev<'_> {
        IntDev::new(&mut self.k, self.p.int)
    }
}

fn name(d: &mut IntDev<'_>, s: &str) -> NameId {
    let anon = d.kernel().anon();
    d.kernel().name_str(anon, s)
}

fn declare(d: &mut IntDev<'_>, tag: &str, vars: &[(u64, ExprId)], concl: ExprId, proof: ExprId) {
    let mut ty = concl;
    let mut value = proof;
    for &(fv, vty) in vars.iter().rev() {
        ty = d.pi_fv(fv, vty, ty);
        value = d.lam_fv(fv, vty, value);
    }
    let n = name(d, tag);
    d.declare_theorem(n, ty, value)
        .unwrap_or_else(|e| panic!("{tag}: kernel rejected the emitted term: {e:?}"));
}

// ---------------------------------------------------------------------------
// 1. three Then goals, neither producer alone
// ---------------------------------------------------------------------------

#[test]
fn then_ring_linarith_order_goal_needs_the_fallback() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let rat_ty = crate::rat_prelude::ops::rat_ty(&mut d);
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);
        let hx_fv = d.fresh_fvar();
        let hy_fv = d.fresh_fvar();
        let zero_c = generic_zero(&mut d, &p);
        let hyp_x_ty = generic_rel(&mut d, &p, LE, zero_c, x);
        let hyp_y_ty = generic_rel(&mut d, &p, LE, zero_c, y);
        let hx = d.kernel().fvar(hx_fv);
        let hy = d.kernel().fvar(hy_fv);

        let sum = generic_rel(&mut d, &p, ADD, x, y);
        let goal = generic_rel(&mut d, &p, LE, zero_c, sum);

        assert!(
            ring::rat::prove(&mut d, &p, goal).is_err(),
            "ring alone must decline a non-Eq (`Alg.OrderedRing.le`) goal outright",
        );

        let assumptions = [(hyp_x_ty, hx), (hyp_y_ty, hy)];
        let ctx = Ctx {
            prelude: p,
            assumptions: &assumptions,
            zero_le_one: None,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Ring), Box::new(Tactic::Linarith));
        let proof = rat::run(&mut d, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Ring, Linarith) declined: {e:?}"));
        declare(
            &mut d,
            "then_ring_linarith_sum_nonneg",
            &[
                (x_fv, rat_ty),
                (y_fv, rat_ty),
                (hx_fv, hyp_x_ty),
                (hy_fv, hyp_y_ty),
            ],
            goal,
            proof,
        );
    });
}

#[test]
fn then_decide_linarith_symbolic_hypothesis_needed() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let x_fv = d.fresh_fvar();
        let rat_ty = crate::rat_prelude::ops::rat_ty(&mut d);
        let x = d.kernel().fvar(x_fv);
        let h_fv = d.fresh_fvar();
        let zero_c = generic_zero(&mut d, &p);
        // `linarith::generic::Problem::parse_prop` only recognises `Le`/`Eq`
        // shapes (no `Lt`), so both the hypothesis and the goal are `Le`
        // here.
        let hyp_ty = generic_rel(&mut d, &p, LE, zero_c, x);
        let h = d.kernel().fvar(h_fv);
        let goal = generic_rel(&mut d, &p, LE, zero_c, x);

        let ctx0 = Ctx {
            prelude: p,
            assumptions: &[],
            zero_le_one: None,
        };
        assert!(
            matches!(
                rat::run(&mut d, &ctx0, &Tactic::Decide, goal),
                Err(Decline::Decide(_))
            ),
            "decide alone must decline a goal with a free variable",
        );

        let assumptions = [(hyp_ty, h)];
        let ctx = Ctx {
            prelude: p,
            assumptions: &assumptions,
            zero_le_one: None,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Decide), Box::new(Tactic::Linarith));
        let proof = rat::run(&mut d, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Decide, Linarith) declined: {e:?}"));
        declare(
            &mut d,
            "then_decide_linarith_lt_to_le",
            &[(x_fv, rat_ty), (h_fv, hyp_ty)],
            goal,
            proof,
        );
    });
}

#[test]
fn then_decide_ring_symbolic_identity_needs_the_fallback() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let x_fv = d.fresh_fvar();
        let rat_ty = crate::rat_prelude::ops::rat_ty(&mut d);
        let x = d.kernel().fvar(x_fv);
        let one_c = d.kernel().const_(p.one, vec![]);
        let mul_name = p.int.rat_mul;
        let lhs = d.lemma(mul_name, &[one_c, x]);
        let goal = req(&mut d, lhs, x);

        let ctx0 = Ctx {
            prelude: p,
            assumptions: &[],
            zero_le_one: None,
        };
        assert!(
            matches!(
                rat::run(&mut d, &ctx0, &Tactic::Decide, goal),
                Err(Decline::Decide(_))
            ),
            "decide alone must decline a goal with a free variable",
        );

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            zero_le_one: None,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Decide), Box::new(Tactic::Ring));
        let proof = rat::run(&mut d, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Decide, Ring) declined: {e:?}"));
        declare(
            &mut d,
            "then_decide_ring_one_mul",
            &[(x_fv, rat_ty)],
            goal,
            proof,
        );
    });
}

// ---------------------------------------------------------------------------
// 2. First, aggregating declines
// ---------------------------------------------------------------------------

#[test]
fn first_aggregates_declines_when_none_apply() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);
        let goal = req(&mut d, x, y); // unrelated free variables, unprovable.

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            zero_le_one: None,
        };
        let list = Tactic::First(vec![Tactic::Decide, Tactic::Ring, Tactic::Linarith]);
        let result = rat::run(&mut d, &ctx, &list, goal);
        match result {
            Err(Decline::First(declines)) => {
                assert_eq!(declines.len(), 3, "expected all three tactics to decline");
            }
            other => panic!("expected Decline::First(3 entries), got {other:?}"),
        }
    });
}

// ---------------------------------------------------------------------------
// 3. a mismatched producer output is rejected by the KERNEL
// ---------------------------------------------------------------------------

#[test]
fn a_mismatched_ring_output_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv); // unrelated to `x`.

        let one_c = d.kernel().const_(p.one, vec![]);
        let mul_name = p.int.rat_mul;
        let lhs = d.lemma(mul_name, &[one_c, x]);
        let true_goal = req(&mut d, lhs, x);
        let term = ring::rat::prove(&mut d, &p, true_goal)
            .unwrap_or_else(|e| panic!("1 * x = x must be provable: {e:?}"));

        // Splice the SAME term in as if it proved `1 * x = y` (false, `x`
        // and `y` unrelated).
        let false_goal = req(&mut d, lhs, y);
        let n = name(&mut d, "corrupted_rat_ring");
        let result = d.declare_theorem(n, false_goal, term);
        assert!(
            result.is_err(),
            "a proof of `1*x = x` must be rejected against the stated goal `1*x = y`"
        );
    });
}
