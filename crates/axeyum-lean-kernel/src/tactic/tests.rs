//! Tests for the `Tactic` combinator.
//!
//! Three batteries:
//!
//! 1. **Five goals closed by `Then(Simp, Linarith)`** that neither producer
//!    closes alone — `pred_succ`/`sub_self`/`sub_zero` (all default
//!    `simp` rules) wrap a variable in an operator `linarith`'s parser
//!    treats as an opaque atom, so `linarith` alone cannot connect it to a
//!    hypothesis about the variable underneath; `simp` alone cannot close
//!    an ORDER goal at all (its own `prove` is `Eq`-only). Each test asserts
//!    BOTH declines directly before showing `Then` succeeds.
//! 2. **Three goals closed by `Then(Simp, Ring)`** — same operators, but the
//!    residual after normalizing needs a genuine `add_comm`/`mul_comm` step
//!    `simp`'s default rule set deliberately does not include (a bare
//!    commutativity law never terminates as a default — see `simp::nat`'s
//!    own module docs), so `simp` alone declines `SidesDiffer`, and `ring`
//!    alone declines/refuses because it cannot see through the
//!    non-ring-fragment operator.
//! 3. **`First([Decide, Linarith, Ring])` on a mix** of goal shapes, plus
//!    the corrupted-glue test: `tactic::glue_rel` (private, reached via
//!    `super::`) spliced with a residue that does NOT actually prove what
//!    it is claimed to, exactly the "does the KERNEL catch it" question
//!    every other producer's corruption tests ask.

#![allow(clippy::many_single_char_names)]

use crate::decide::Shape;
use crate::linarith;
use crate::ring;
use crate::simp;
use crate::tactic::{self, Ctx, Decline, Tactic};
use crate::{
    ExprId, Kernel, NameId, NatOps, NatPrelude, NatState, build_nat_prelude, on_a_deep_stack,
};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
    root: NameId,
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
        let anon = k.anon();
        let root = k.name_str(anon, "tactic_test");
        Self { k, p, st, root }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }
}

/// Universally quantify `concl` (with hypotheses `hyp_types`) over `fvs` and
/// `hyp_fvs`, and require the KERNEL to accept the resulting declaration.
fn declare(
    f: &mut Fixture,
    tag: &str,
    fvs: &[u64],
    hyp_types: &[ExprId],
    hyp_fvs: &[u64],
    concl: ExprId,
    proof: ExprId,
) {
    let nat = f.nat_ty();
    let mut ty = concl;
    let mut value = proof;
    for (&hty, &hfv) in hyp_types.iter().zip(hyp_fvs.iter()).rev() {
        ty = f.arrow(hty, ty);
        value = f.lam_fv(hfv, hty, value);
    }
    for &fv in fvs.iter().rev() {
        ty = f.pi_fv(fv, nat, ty);
        value = f.lam_fv(fv, nat, value);
    }
    let name = f.name(tag);
    f.declare_theorem(name, ty, value)
        .unwrap_or_else(|e| panic!("{tag}: kernel rejected the emitted term: {e:?}"));
}

// ---------------------------------------------------------------------------
// 1. Then(Simp, Linarith): five goals, neither producer alone
// ---------------------------------------------------------------------------

#[test]
fn then_simp_linarith_pred_succ_le_with_hypothesis() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);
        let hyp_ty = f.le(n, m);
        let h_fv = f.fresh_fvar();
        let h = f.k.fvar(h_fv);

        let sn = f.succ(n);
        let pred_sn = f.pred(sn);
        let goal = f.le(pred_sn, m);

        let assumptions = [(hyp_ty, h)];
        assert!(
            linarith::nat::prove(&mut f, &p, &assumptions, goal).is_err(),
            "linarith alone must not see through `pred (succ n)`",
        );
        let rules = simp::nat::default_rules::<Fixture>(&p);
        assert!(
            simp::nat::prove(&mut f, &p, &rules, goal).is_err(),
            "simp alone cannot close a `Le` goal (its `prove` is `Eq`-only)",
        );

        let ctx = Ctx {
            prelude: p,
            assumptions: &assumptions,
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Linarith) declined: {e:?}"));
        declare(
            &mut f,
            "pred_succ_le_hyp",
            &[n_fv, m_fv],
            &[hyp_ty],
            &[h_fv],
            goal,
            proof,
        );
    });
}

#[test]
fn then_simp_linarith_sub_self_le_no_hypotheses() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);

        let sub_nn = f.sub(n, n);
        let goal = f.le(sub_nn, m);

        assert!(
            linarith::nat::prove(&mut f, &p, &[], goal).is_err(),
            "linarith alone must not see through `sub n n`",
        );
        let rules = simp::nat::default_rules::<Fixture>(&p);
        assert!(simp::nat::prove(&mut f, &p, &rules, goal).is_err());

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Linarith) declined: {e:?}"));
        declare(
            &mut f,
            "sub_self_le_no_hyp",
            &[n_fv, m_fv],
            &[],
            &[],
            goal,
            proof,
        );
    });
}

#[test]
fn then_simp_linarith_sub_self_lt_no_hypotheses() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);

        let sub_nn = f.sub(n, n);
        let sm = f.succ(m);
        let goal = f.lt(sub_nn, sm);

        assert!(linarith::nat::prove(&mut f, &p, &[], goal).is_err());
        let rules = simp::nat::default_rules::<Fixture>(&p);
        assert!(simp::nat::prove(&mut f, &p, &rules, goal).is_err());

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Linarith) declined: {e:?}"));
        declare(
            &mut f,
            "sub_self_lt_no_hyp",
            &[n_fv, m_fv],
            &[],
            &[],
            goal,
            proof,
        );
    });
}

#[test]
fn then_simp_linarith_sub_zero_le_with_hypothesis() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);
        let hyp_ty = f.le(n, m);
        let h_fv = f.fresh_fvar();
        let h = f.k.fvar(h_fv);

        let zero = f.zero();
        let sub_n0 = f.sub(n, zero);
        let goal = f.le(sub_n0, m);

        let assumptions = [(hyp_ty, h)];
        assert!(
            linarith::nat::prove(&mut f, &p, &assumptions, goal).is_err(),
            "linarith alone must not see through `sub n zero`",
        );
        let rules = simp::nat::default_rules::<Fixture>(&p);
        assert!(simp::nat::prove(&mut f, &p, &rules, goal).is_err());

        let ctx = Ctx {
            prelude: p,
            assumptions: &assumptions,
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Linarith) declined: {e:?}"));
        declare(
            &mut f,
            "sub_zero_le_hyp",
            &[n_fv, m_fv],
            &[hyp_ty],
            &[h_fv],
            goal,
            proof,
        );
    });
}

#[test]
fn then_simp_linarith_pred_succ_lt_with_hypothesis() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);
        let hyp_ty = f.le(n, m);
        let h_fv = f.fresh_fvar();
        let h = f.k.fvar(h_fv);

        let sn = f.succ(n);
        let pred_sn = f.pred(sn);
        let sm = f.succ(m);
        let goal = f.lt(pred_sn, sm);

        let assumptions = [(hyp_ty, h)];
        assert!(
            linarith::nat::prove(&mut f, &p, &assumptions, goal).is_err(),
            "linarith alone must not see through `pred (succ n)` inside `succ`",
        );
        let rules = simp::nat::default_rules::<Fixture>(&p);
        assert!(simp::nat::prove(&mut f, &p, &rules, goal).is_err());

        let ctx = Ctx {
            prelude: p,
            assumptions: &assumptions,
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Linarith) declined: {e:?}"));
        declare(
            &mut f,
            "pred_succ_lt_hyp",
            &[n_fv, m_fv],
            &[hyp_ty],
            &[h_fv],
            goal,
            proof,
        );
    });
}

// ---------------------------------------------------------------------------
// 2. Then(Simp, Ring): three goals, neither producer alone
// ---------------------------------------------------------------------------

#[test]
fn then_simp_ring_pred_succ_add_comm() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);

        let sn = f.succ(n);
        let pred_sn = f.pred(sn);
        let lhs = f.add(m, pred_sn);
        let rhs = f.add(n, m);
        let goal = f.eq(lhs, rhs);

        assert!(
            ring::nat::prove(&mut f, &p, goal).is_err(),
            "ring alone treats `pred (succ n)` as an atom distinct from `n`",
        );
        let rules = simp::nat::default_rules::<Fixture>(&p);
        assert!(
            simp::nat::prove(&mut f, &p, &rules, goal).is_err(),
            "simp alone leaves `m + n` vs `n + m` -- no `add_comm` default rule",
        );

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Ring));
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Ring) declined: {e:?}"));
        declare(
            &mut f,
            "pred_succ_add_comm",
            &[n_fv, m_fv],
            &[],
            &[],
            goal,
            proof,
        );
    });
}

#[test]
fn then_simp_ring_sub_zero_add_comm() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);

        let zero = f.zero();
        let sub_n0 = f.sub(n, zero);
        let lhs = f.add(m, sub_n0);
        let rhs = f.add(n, m);
        let goal = f.eq(lhs, rhs);

        assert!(
            ring::nat::prove(&mut f, &p, goal).is_err(),
            "ring alone declines `NonRing` on `sub`",
        );
        let rules = simp::nat::default_rules::<Fixture>(&p);
        assert!(simp::nat::prove(&mut f, &p, &rules, goal).is_err());

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Ring));
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Ring) declined: {e:?}"));
        declare(
            &mut f,
            "sub_zero_add_comm",
            &[n_fv, m_fv],
            &[],
            &[],
            goal,
            proof,
        );
    });
}

#[test]
fn then_simp_ring_pred_succ_mul_comm() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);

        let sn = f.succ(n);
        let pred_sn = f.pred(sn);
        let lhs = f.mul(m, pred_sn);
        let rhs = f.mul(n, m);
        let goal = f.eq(lhs, rhs);

        assert!(
            ring::nat::prove(&mut f, &p, goal).is_err(),
            "ring alone treats `pred (succ n)` as an atom distinct from `n`",
        );
        let rules = simp::nat::default_rules::<Fixture>(&p);
        assert!(simp::nat::prove(&mut f, &p, &rules, goal).is_err());

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &rules,
        };
        let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Ring));
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("Then(Simp, Ring) declined: {e:?}"));
        declare(
            &mut f,
            "pred_succ_mul_comm",
            &[n_fv, m_fv],
            &[],
            &[],
            goal,
            proof,
        );
    });
}

// ---------------------------------------------------------------------------
// 3. First([Decide, Linarith, Ring]) on a mix, and total failure
// ---------------------------------------------------------------------------

fn mix() -> Tactic {
    Tactic::First(vec![Tactic::Decide, Tactic::Linarith, Tactic::Ring])
}

#[test]
fn first_decide_wins_on_a_closed_goal() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let sum = f.add(two, three);
        let goal = f.eq(sum, five);

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &[],
        };
        let tactic = mix();
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("First declined: {e:?}"));
        let name = f.name("first_decide_wins");
        f.declare_theorem(name, goal, proof)
            .unwrap_or_else(|e| panic!("kernel rejected: {e:?}"));
    });
}

#[test]
fn first_linarith_wins_after_decide_declines() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);
        let hyp_ty = f.le(n, m);
        let h_fv = f.fresh_fvar();
        let h = f.k.fvar(h_fv);
        let goal = f.le(n, m);

        let assumptions = [(hyp_ty, h)];
        let ctx = Ctx {
            prelude: p,
            assumptions: &assumptions,
            rules: &[],
        };
        let tactic = mix();
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("First declined: {e:?}"));
        declare(
            &mut f,
            "first_linarith_wins",
            &[n_fv, m_fv],
            &[hyp_ty],
            &[h_fv],
            goal,
            proof,
        );
    });
}

#[test]
fn first_ring_wins_after_decide_and_linarith_decline() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);
        let lhs = f.mul(n, m);
        let rhs = f.mul(m, n);
        let goal = f.eq(lhs, rhs);

        assert!(
            crate::decide::run(&mut f, &p, goal).is_err(),
            "decide must decline on a goal with free variables",
        );
        assert!(
            linarith::nat::prove(&mut f, &p, &[], goal).is_err(),
            "linarith must decline `NonLinear` on a product of two variables",
        );

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &[],
        };
        let tactic = mix();
        let proof = tactic::run(&mut f, &ctx, &tactic, goal)
            .unwrap_or_else(|e| panic!("First declined: {e:?}"));
        declare(
            &mut f,
            "first_ring_wins",
            &[n_fv, m_fv],
            &[],
            &[],
            goal,
            proof,
        );
    });
}

#[test]
fn first_declines_with_every_sub_decline_when_all_three_fail() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);
        let pn = f.pred(n);
        let goal = f.eq(pn, m);

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            rules: &[],
        };
        let tactic = mix();
        match tactic::run(&mut f, &ctx, &tactic, goal) {
            Err(Decline::First(declines)) => {
                assert_eq!(declines.len(), 3, "one decline per tried tactic");
            }
            other => panic!("expected Decline::First with 3 entries, got {other:?}"),
        }
    });
}

// ---------------------------------------------------------------------------
// corrupted glue is rejected by the KERNEL
// ---------------------------------------------------------------------------

#[test]
fn corrupted_glue_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m = f.k.fvar(m_fv);
        let goal = f.le(n, m);

        let hl = f.refl(n);
        let hr = f.refl(m);
        // The WRONG residue: a proof of `Le m m`, not `Le n m`.
        let wrong_residue = f.lemma(p.le_refl, &[m]);
        let glued = super::glue_rel(&mut f, Shape::Le, n, n, hl, m, m, hr, wrong_residue);

        let nat = f.nat_ty();
        let ty = f.pi_fv(m_fv, nat, goal);
        let ty = f.pi_fv(n_fv, nat, ty);
        let value = f.lam_fv(m_fv, nat, glued);
        let value = f.lam_fv(n_fv, nat, value);
        let name = f.name("corrupted_glue");
        let verdict = f.declare_theorem(name, ty, value);
        assert!(
            verdict.is_err(),
            "the kernel admitted a `Le m m` glued term at type `Le n m`",
        );
    });
}
