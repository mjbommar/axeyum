//! Tests for the ℤ `Tactic` combinator.
//!
//! Two batteries:
//!
//! 1. **Three goals closed by `Then(Simp, Linarith)`** that neither
//!    producer closes alone. Each wraps a COMPOUND argument in `Int.neg`
//!    (`neg (add x y)`) — `linarith::int`'s own module docs: "`Int.neg`
//!    applied to a compound term is treated as an opaque atom rather than
//!    distributed with `neg_add`" — so `linarith` alone cannot connect it
//!    to the `x`/`y` on the other side; `simp`'s default `neg_add` rule
//!    distributes it (`neg (add x y) = add (neg x) (neg y)`), which
//!    `linarith` DOES parse exactly (`neg` of an atom is handled exactly).
//!    `simp` alone cannot close an ORDER goal at all (`Tactic::Simp`'s own
//!    goal parser is `Eq`-only). Each test asserts both declines directly
//!    before showing `Then` succeeds.
//!
//!    (No `Then(Simp, Ring)` battery: `ring::int` already distributes `neg`/
//!    `sub` over `add`/`mul` fully as part of its own normal form
//!    (`ring::int`'s own module docs: "`neg`/`sub` are ring operations
//!    here, not declined … `neg` of a compound distributes fully"), so
//!    every shape `simp`'s default `neg_add`/`mul_neg` rules could expose
//!    is ALREADY inside `ring::int`'s own fragment — a genuine "`simp`
//!    needed before `ring` can close it" case does not exist for the
//!    default rule set the way it does for `ring::nat`'s narrower
//!    fragment. A measured negative, not an oversight.)
//! 2. **`First([Decide, Linarith, Ring])`** on a mix, plus the
//!    corrupted-glue test.

#![allow(clippy::many_single_char_names)]

use super::glue_rel;
use crate::decide::Shape;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::linarith;
use crate::nat_prelude::NatOps;
use crate::simp;
use crate::tactic::int::{self, Ctx, Decline, Tactic};
use crate::{IntPrelude, Kernel, NameId, build_int_prelude, on_a_deep_stack};

struct Fixture {
    k: Kernel,
    p: IntPrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_int_prelude(&mut k).expect("Int prelude must build");
        Self { k, p }
    }

    fn dev(&mut self) -> IntDev<'_> {
        IntDev::new(&mut self.k, self.p)
    }
}

fn name(d: &mut IntDev<'_>, s: &str) -> NameId {
    let anon = d.kernel().anon();
    d.kernel().name_str(anon, s)
}

/// Universally quantify `concl`/`proof` over `fvs` (all `Int`-typed) and
/// require the KERNEL to accept the resulting declaration.
fn declare(d: &mut IntDev<'_>, tag: &str, fvs: &[u64], concl: ExprId, proof: ExprId) {
    let int_ty = d.int_ty();
    let mut ty = concl;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, int_ty, ty);
        value = d.lam_fv(fv, int_ty, value);
    }
    let n = name(d, tag);
    d.declare_theorem(n, ty, value)
        .unwrap_or_else(|e| panic!("{tag}: kernel rejected the emitted term: {e:?}"));
}

fn assert_neither_closes_alone(
    p: &IntPrelude,
    d: &mut IntDev<'_>,
    goal: ExprId,
    rules: &[simp::int::Rule],
) {
    assert!(
        linarith::int::prove(d, p, &[], goal).is_err(),
        "linarith alone must not see through `neg (add x y)`",
    );
    let ctx = Ctx {
        prelude: *p,
        assumptions: &[],
        rules,
    };
    assert!(
        matches!(
            int::run(d, &ctx, &Tactic::Simp, goal),
            Err(Decline::Simp(_))
        ),
        "simp alone cannot close an order goal (its own `prove` is `Eq`-only)",
    );
}

// ---------------------------------------------------------------------------
// 1. Then(Simp, Linarith): three goals, neither producer alone
// ---------------------------------------------------------------------------

#[test]
fn then_simp_linarith_neg_add_lt_one_more() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);

        // neg (x + y) < (neg x + neg y) + 1 -- an EXACT tautology once the
        // LHS is distributed; `Z < -x + -y + 1` for an opaque `Z` otherwise.
        let xy = d.iadd(x, y);
        let lhs = d.ineg(xy);
        let nx = d.ineg(x);
        let ny = d.ineg(y);
        let nxny = d.iadd(nx, ny);
        let one = d.ione();
        let rhs = d.iadd(nxny, one);
        let goal = d.ilt(lhs, rhs);

        let rules = simp::int::default_rules(&p);
        assert_neither_closes_alone(&p, &mut d, goal, &rules);

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));
        let proof = int::run(&mut d, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Linarith) declined: {e:?}"));
        declare(&mut d, "neg_add_lt_one_more", &[x_fv, y_fv], goal, proof);
    });
}

#[test]
fn then_simp_linarith_neg_add_le_itself() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);

        // neg (x + y) <= neg x + neg y -- an EXACT (residual 0) tautology
        // once distributed.
        let xy = d.iadd(x, y);
        let lhs = d.ineg(xy);
        let nx = d.ineg(x);
        let ny = d.ineg(y);
        let rhs = d.iadd(nx, ny);
        let goal = d.ile(lhs, rhs);

        let rules = simp::int::default_rules(&p);
        assert_neither_closes_alone(&p, &mut d, goal, &rules);

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));
        let proof = int::run(&mut d, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Linarith) declined: {e:?}"));
        declare(&mut d, "neg_add_le_itself", &[x_fv, y_fv], goal, proof);
    });
}

#[test]
fn then_simp_linarith_neg_add_lt_with_hypothesis() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let h_fv = d.fresh_fvar();

        // hyp: neg x + neg y < z.  goal: neg (x + y) < z.
        let nx = d.ineg(x);
        let ny = d.ineg(y);
        let nxny = d.iadd(nx, ny);
        let hyp_ty = d.ilt(nxny, z);
        let h = d.kernel().fvar(h_fv);

        let xy = d.iadd(x, y);
        let lhs = d.ineg(xy);
        let goal = d.ilt(lhs, z);

        let rules = simp::int::default_rules(&p);
        let assumptions = [(hyp_ty, h)];
        assert!(
            linarith::int::prove(&mut d, &p, &assumptions, goal).is_err(),
            "linarith alone must not see through `neg (add x y)`",
        );
        let ctx0 = Ctx {
            prelude: p,
            assumptions: &assumptions,
            rules: &rules,
        };
        assert!(
            matches!(
                int::run(&mut d, &ctx0, &Tactic::Simp, goal),
                Err(Decline::Simp(_))
            ),
            "simp alone cannot close an order goal",
        );

        let ctx = Ctx {
            prelude: p,
            assumptions: &assumptions,
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));
        let proof = int::run(&mut d, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Linarith) declined: {e:?}"));
        let concl = d.pi_fv(h_fv, hyp_ty, goal);
        let value = d.lam_fv(h_fv, hyp_ty, proof);
        declare(
            &mut d,
            "neg_add_lt_with_hyp",
            &[x_fv, y_fv, z_fv],
            concl,
            value,
        );
    });
}

// ---------------------------------------------------------------------------
// 2. First, and the corrupted-glue test
// ---------------------------------------------------------------------------

#[test]
fn first_decide_linarith_ring_on_a_mix() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let rules = simp::int::default_rules(&p);
        let list = Tactic::First(vec![Tactic::Decide, Tactic::Linarith, Tactic::Ring]);

        // decide wins: a closed goal.
        {
            let two_a = {
                let n = d.num(2);
                d.of_nat(n)
            };
            let two_b = {
                let n = d.num(2);
                d.of_nat(n)
            };
            let goal = d.ieq(two_a, two_b);
            let ctx = Ctx {
                prelude: p,
                assumptions: &[],
                rules: &rules,
            };
            let proof = int::run(&mut d, &ctx, &list, goal)
                .unwrap_or_else(|e| panic!("decide-winnable goal declined: {e:?}"));
            declare(&mut d, "first_decide_wins", &[], goal, proof);
        }

        // ring wins after decide/linarith decline: a symbolic ring identity.
        {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let one = d.ione();
            let lhs = d.imul(one, x);
            let goal = d.ieq(lhs, x);
            let ctx = Ctx {
                prelude: p,
                assumptions: &[],
                rules: &rules,
            };
            let proof = int::run(&mut d, &ctx, &list, goal)
                .unwrap_or_else(|e| panic!("ring-winnable goal declined: {e:?}"));
            declare(&mut d, "first_ring_wins", &[x_fv], goal, proof);
        }

        // all three decline: an unprovable symbolic goal, aggregated.
        {
            let x_fv = d.fresh_fvar();
            let y_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let y = d.kernel().fvar(y_fv);
            let goal = d.ieq(x, y);
            let ctx = Ctx {
                prelude: p,
                assumptions: &[],
                rules: &rules,
            };
            let result = int::run(&mut d, &ctx, &list, goal);
            match result {
                Err(Decline::First(declines)) => {
                    assert_eq!(declines.len(), 3, "expected all three tactics to decline");
                }
                other => panic!("expected Decline::First(3 entries), got {other:?}"),
            }
        }
    });
}

#[test]
fn a_corrupted_glue_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let n_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m = d.kernel().fvar(m_fv);
        let goal = d.ile(n, m);

        let hl = d.irefl(n);
        let hr = d.irefl(m);
        // The WRONG residue: a proof of `Int.le m m`, not `Int.le n m`.
        let wrong_residue = d.lemma(p.le_refl, &[m]);
        let glued = glue_rel(&mut d, Shape::Le, n, n, hl, m, m, hr, wrong_residue);

        let int_ty = d.int_ty();
        let ty = d.pi_fv(m_fv, int_ty, goal);
        let ty = d.pi_fv(n_fv, int_ty, ty);
        let value = d.lam_fv(m_fv, int_ty, glued);
        let value = d.lam_fv(n_fv, int_ty, value);
        let nm = name(&mut d, "corrupted_int_glue");
        let result = d.declare_theorem(nm, ty, value);
        assert!(
            result.is_err(),
            "the kernel admitted an `Int.le m m` glued term at type `Int.le n m`",
        );
    });
}
