//! Tests for the ℕ linear-arithmetic producer.
//!
//! Four batteries, and the third is the one that decides whether any of this
//! is worth anything:
//!
//! 1. **The ten retirement targets.** Each is proved by the procedure and the
//!    emitted term is admitted through `Kernel::add_declaration` at a type the
//!    test requires to be *definitionally equal to the prelude's own
//!    hand-proved statement*. A type read off the emitted term would only
//!    measure the emitter against itself.
//! 2. **False goals decline.** Three goals that are simply not true get
//!    `Decline::NoCertificate` and no term at all.
//! 3. **Corrupted certificates are rejected by the KERNEL.** A coefficient off
//!    by one, a residual off by one, and a hypothesis swapped for another
//!    lemma's proof: in each case the procedure *emits a term* and
//!    `add_declaration` refuses it. If the procedure's own bookkeeping were the
//!    only thing catching these, the trust story would be circular — so the
//!    corruption tests deliberately run with the internal check disabled.
//! 4. **The fragment's boundary.** A goal containing a product of two
//!    variables is refused by the parser with `Decline::NonLinear`, and the
//!    positive control beside it — the same goal with a numeral multiplier —
//!    is proved. A refusal test with no positive control cannot tell "outside
//!    the fragment" from "the parser is broken".

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::linarith::nat as linarith;
use crate::linarith::{Certificate, Decline, LinForm};
use crate::{
    ExprId, Kernel, NameId, NatOps, NatPrelude, NatState, build_nat_prelude, on_a_deep_stack,
};

/// A development over a kernel carrying the `Nat` prelude.
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
        let root = k.name_str(anon, "linarith_test");
        Self { k, p, st, root }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }

    /// The type the prelude's own hand-written proof was admitted at.
    fn prelude_type(&self, name: NameId) -> ExprId {
        self.k
            .environment()
            .get(name)
            .expect("the prelude declares this name")
            .ty()
    }
}

/// Declare `label` by the procedure and require its type to be definitionally
/// equal to the prelude's existing statement of `mirror`.
///
/// The comparison is against the **prelude's** type, never against the one the
/// emitter produced: a test that reads its expectation off the thing under test
/// measures nothing.
fn retire(
    label: &str,
    mirror: fn(&NatPrelude) -> NameId,
    arity: usize,
    build: &dyn Fn(&mut Fixture, &[ExprId]) -> (Vec<ExprId>, ExprId),
) {
    let mut f = Fixture::new();
    let p = f.p;
    let expected = f.prelude_type(mirror(&p));
    let name = f.name(label);
    let ty = linarith::theorem(&mut f, &p, name, arity, build)
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(
        f.k.def_eq(ty, expected),
        "{label}: the emitted declaration's type is not the prelude's statement",
    );
    assert!(
        f.k.environment().contains(name),
        "{label}: the kernel did not learn the name",
    );
}

// ---------------------------------------------------------------------------
// 1. the ten retirement targets
// ---------------------------------------------------------------------------

#[test]
fn target_le_refl_thm() {
    on_a_deep_stack(|| {
        retire("le_refl_thm", |p| p.le_refl_thm, 1, &|d, v| {
            let concl = d.le(v[0], v[0]);
            (vec![], concl)
        });
    });
}

#[test]
fn target_le_succ() {
    on_a_deep_stack(|| {
        retire("le_succ", |p| p.le_succ, 1, &|d, v| {
            let s = d.succ(v[0]);
            let concl = d.le(v[0], s);
            (vec![], concl)
        });
    });
}

#[test]
fn target_succ_le_succ() {
    on_a_deep_stack(|| {
        retire("succ_le_succ", |p| p.succ_le_succ, 2, &|d, v| {
            let hyp = d.le(v[0], v[1]);
            let sn = d.succ(v[0]);
            let sm = d.succ(v[1]);
            let concl = d.le(sn, sm);
            (vec![hyp], concl)
        });
    });
}

#[test]
fn target_le_of_lt_succ() {
    on_a_deep_stack(|| {
        retire("le_of_lt_succ", |p| p.le_of_lt_succ, 2, &|d, v| {
            let sm = d.succ(v[1]);
            let hyp = d.lt(v[0], sm);
            let concl = d.le(v[0], v[1]);
            (vec![hyp], concl)
        });
    });
}

#[test]
fn target_lt_succ_self() {
    on_a_deep_stack(|| {
        retire("lt_succ_self", |p| p.lt_succ_self, 1, &|d, v| {
            let s = d.succ(v[0]);
            let concl = d.lt(v[0], s);
            (vec![], concl)
        });
    });
}

#[test]
fn target_lt_succ_of_le() {
    on_a_deep_stack(|| {
        retire("lt_succ_of_le", |p| p.lt_succ_of_le, 2, &|d, v| {
            let hyp = d.le(v[0], v[1]);
            let sm = d.succ(v[1]);
            let concl = d.lt(v[0], sm);
            (vec![hyp], concl)
        });
    });
}

#[test]
fn target_lt_add_one() {
    on_a_deep_stack(|| {
        retire("lt_add_one", |p| p.lt_add_one, 1, &|d, v| {
            let one = d.num(1);
            let n1 = d.add(v[0], one);
            let concl = d.lt(v[0], n1);
            (vec![], concl)
        });
    });
}

#[test]
fn target_le_succ_of_le() {
    on_a_deep_stack(|| {
        retire("le_succ_of_le", |p| p.le_succ_of_le, 2, &|d, v| {
            let hyp = d.le(v[0], v[1]);
            let sm = d.succ(v[1]);
            let concl = d.le(v[0], sm);
            (vec![hyp], concl)
        });
    });
}

#[test]
fn target_zero_lt_succ() {
    on_a_deep_stack(|| {
        retire("zero_lt_succ", |p| p.zero_lt_succ, 1, &|d, v| {
            let zero = d.zero();
            let s = d.succ(v[0]);
            let concl = d.lt(zero, s);
            (vec![], concl)
        });
    });
}

#[test]
fn target_le_of_lt_add_one() {
    on_a_deep_stack(|| {
        retire("le_of_lt_add_one", |p| p.le_of_lt_add_one, 2, &|d, v| {
            let one = d.num(1);
            let b1 = d.add(v[1], one);
            let hyp = d.lt(v[0], b1);
            let concl = d.le(v[0], v[1]);
            (vec![hyp], concl)
        });
    });
}

// ---------------------------------------------------------------------------
// 2. false goals decline
// ---------------------------------------------------------------------------

/// The procedure's answer for `concl` under `hyps`, with no declaration made.
fn attempt(
    arity: usize,
    build: &dyn Fn(&mut Fixture, &[ExprId]) -> (Vec<ExprId>, ExprId),
) -> Result<ExprId, Decline> {
    let mut f = Fixture::new();
    let p = f.p;
    let vars: Vec<ExprId> = (0..arity)
        .map(|_| {
            let fv = f.fresh_fvar();
            f.k.fvar(fv)
        })
        .collect();
    let (hyp_types, concl) = build(&mut f, &vars);
    let assumptions: Vec<linarith::Assumption> = hyp_types
        .iter()
        .map(|&ty| {
            let fv = f.fresh_fvar();
            let h = f.k.fvar(fv);
            (ty, h)
        })
        .collect();
    linarith::prove(&mut f, &p, &assumptions, concl)
}

#[test]
fn a_false_order_goal_declines() {
    on_a_deep_stack(|| {
        // `succ n ≤ n` — false at every n.
        let got = attempt(1, &|d, v| {
            let s = d.succ(v[0]);
            let concl = d.le(s, v[0]);
            (vec![], concl)
        });
        assert_eq!(got.err(), Some(Decline::NoCertificate));
    });
}

#[test]
fn a_false_goal_with_a_true_hypothesis_declines() {
    on_a_deep_stack(|| {
        // from `n ≤ m`, conclude `m ≤ n` — false in general.
        let got = attempt(2, &|d, v| {
            let hyp = d.le(v[0], v[1]);
            let concl = d.le(v[1], v[0]);
            (vec![hyp], concl)
        });
        assert_eq!(got.err(), Some(Decline::NoCertificate));
    });
}

#[test]
fn a_false_strict_goal_declines() {
    on_a_deep_stack(|| {
        // `n < n`.
        let got = attempt(1, &|d, v| {
            let concl = d.lt(v[0], v[0]);
            (vec![], concl)
        });
        assert_eq!(got.err(), Some(Decline::NoCertificate));
    });
}

// ---------------------------------------------------------------------------
// 3. corrupted certificates — the KERNEL must be the one that refuses
// ---------------------------------------------------------------------------

/// Set up `n ≤ m ⊢ succ n ≤ succ m`, hand `cert` to the emitter with the
/// internal arithmetic check **disabled**, and return what the kernel says
/// about the resulting term.
fn kernel_verdict_on(cert: &Certificate, swap_hypothesis_proof: bool) -> Result<ExprId, String> {
    let mut f = Fixture::new();
    let p = f.p;
    let n_fv = f.fresh_fvar();
    let m_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let m = f.k.fvar(m_fv);
    let hyp_ty = f.le(n, m);
    let h_fv = f.fresh_fvar();
    let h = f.k.fvar(h_fv);
    // The swap gives the emitter a proof of a DIFFERENT true fact under a type
    // that says `n ≤ m`: `le_add_right n m : n ≤ n + m`.
    let proof = if swap_hypothesis_proof {
        f.lemma(p.le_add_right, &[n, m])
    } else {
        h
    };
    let sn = f.succ(n);
    let sm = f.succ(m);
    let term = linarith::emit_le_from_certificate(
        &mut f,
        &p,
        &[(hyp_ty, proof)],
        sn,
        sm,
        cert,
        /* verify */ false,
    )
    .map_err(|d| format!("the procedure declined instead of emitting: {d:?}"))?;

    let concl = f.le(sn, sm);
    let ty = f.arrow(hyp_ty, concl);
    let value = f.lam_fv(h_fv, hyp_ty, term);
    let nat = f.nat_ty();
    let ty = f.pi_fv(m_fv, nat, ty);
    let value = f.lam_fv(m_fv, nat, value);
    let ty = f.pi_fv(n_fv, nat, ty);
    let value = f.lam_fv(n_fv, nat, value);
    let name = f.name("corrupted");
    match f.declare_theorem(name, ty, value) {
        Ok(()) => Ok(ty),
        Err(e) => Err(format!("{e:?}")),
    }
}

/// The honest certificate for `n ≤ m ⊢ succ n ≤ succ m`: one copy of the
/// hypothesis, no slack.
fn honest_certificate() -> Certificate {
    Certificate {
        multipliers: vec![1],
        residual: LinForm::zero(),
    }
}

#[test]
fn the_honest_certificate_is_the_positive_control() {
    on_a_deep_stack(|| {
        // Without this, every corruption below could be "rejected" for a reason
        // unrelated to the corruption.
        kernel_verdict_on(&honest_certificate(), false)
            .expect("the uncorrupted certificate must be admitted");
    });
}

#[test]
fn a_multiplier_off_by_one_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let cert = Certificate {
            multipliers: vec![2],
            residual: LinForm::zero(),
        };
        let verdict = kernel_verdict_on(&cert, false);
        assert!(
            verdict.is_err(),
            "the kernel admitted a term built from a multiplier-2 certificate \
             for a goal needing exactly one copy",
        );
    });
}

#[test]
fn a_residual_off_by_one_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let cert = Certificate {
            multipliers: vec![1],
            residual: LinForm::constant(1),
        };
        let verdict = kernel_verdict_on(&cert, false);
        assert!(
            verdict.is_err(),
            "the kernel admitted a term whose slack was one larger than the \
             certificate's identity allows",
        );
    });
}

#[test]
fn a_swapped_hypothesis_proof_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        // The arithmetic is untouched — only the *proof* handed in for the
        // hypothesis is a different (true!) fact. Nothing in the procedure
        // looks at a proof term, so only the kernel can catch this.
        let verdict = kernel_verdict_on(&honest_certificate(), true);
        assert!(
            verdict.is_err(),
            "the kernel admitted a term whose hypothesis slot carried a proof \
             of a different proposition",
        );
    });
}

#[test]
fn the_procedures_own_check_also_catches_a_corrupted_certificate() {
    on_a_deep_stack(|| {
        // Same corruption, `verify = true`: the procedure declines rather than
        // emitting. Both answers are useful, and only running one of them would
        // leave the trust story circular.
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
        let sm = f.succ(m);
        let cert = Certificate {
            multipliers: vec![2],
            residual: LinForm::zero(),
        };
        let got =
            linarith::emit_le_from_certificate(&mut f, &p, &[(hyp_ty, h)], sn, sm, &cert, true);
        assert_eq!(got.err(), Some(Decline::NoCertificate));
    });
}

// ---------------------------------------------------------------------------
// 4. the fragment's boundary
// ---------------------------------------------------------------------------

#[test]
fn a_goal_with_a_variable_multiplication_is_refused() {
    on_a_deep_stack(|| {
        // `n ≤ n * m` is TRUE for m ≥ 1 and false at m = 0, but that is not
        // why it is refused: `n * m` is outside the linear fragment and the
        // parser says so rather than abstracting it.
        let got = attempt(2, &|d, v| {
            let prod = d.mul(v[0], v[1]);
            let concl = d.le(v[0], prod);
            (vec![], concl)
        });
        assert_eq!(got.err(), Some(Decline::NonLinear));
    });
}

#[test]
fn the_same_goal_with_a_numeral_multiplier_is_proved() {
    on_a_deep_stack(|| {
        // The positive control for the refusal above: `n ≤ n * 3` IS in the
        // fragment, and the procedure proves it. Without this, the refusal test
        // could not distinguish "outside the fragment" from "the parser is
        // broken".
        let mut f = Fixture::new();
        let p = f.p;
        let name = f.name("le_mul_three");
        let ty = linarith::theorem(&mut f, &p, name, 1, &|d, v| {
            let three = d.num(3);
            let prod = d.mul(v[0], three);
            let concl = d.le(v[0], prod);
            (vec![], concl)
        })
        .expect("n ≤ n * 3 is in the fragment");
        assert!(f.k.environment().contains(name));
        let _ = ty;
    });
}

#[test]
fn a_numeral_multiplier_on_the_left_is_proved_too() {
    on_a_deep_stack(|| {
        // `Nat.mul` recurses on its RIGHT argument, so `mul 3 n` is stuck where
        // `mul n 3` unrolls. The emitter commutes first; this test is what
        // would fail if it did not.
        let mut f = Fixture::new();
        let p = f.p;
        let name = f.name("le_three_mul");
        linarith::theorem(&mut f, &p, name, 1, &|d, v| {
            let three = d.num(3);
            let prod = d.mul(three, v[0]);
            let concl = d.le(v[0], prod);
            (vec![], concl)
        })
        .expect("n ≤ 3 * n is in the fragment");
        assert!(f.k.environment().contains(name));
    });
}

// ---------------------------------------------------------------------------
// the shapes the ten targets do not exercise
// ---------------------------------------------------------------------------

#[test]
fn a_multi_hypothesis_chain_is_proved() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let name = f.name("chain_of_three");
        linarith::theorem(&mut f, &p, name, 4, &|d, v| {
            let h1 = d.le(v[0], v[1]);
            let h2 = d.le(v[1], v[2]);
            let h3 = d.le(v[2], v[3]);
            let concl = d.le(v[0], v[3]);
            (vec![h1, h2, h3], concl)
        })
        .expect("a ≤ b ≤ c ≤ d gives a ≤ d");
        assert!(f.k.environment().contains(name));
    });
}

#[test]
fn an_equality_goal_is_proved_by_antisymmetry() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let name = f.name("eq_of_two_bounds");
        linarith::theorem(&mut f, &p, name, 2, &|d, v| {
            let h1 = d.le(v[0], v[1]);
            let h2 = d.le(v[1], v[0]);
            let concl = d.eq(v[0], v[1]);
            (vec![h1, h2], concl)
        })
        .expect("a ≤ b and b ≤ a give a = b");
        assert!(f.k.environment().contains(name));
    });
}

#[test]
fn an_equality_hypothesis_is_used_in_both_directions() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let name = f.name("le_of_eq_shift");
        linarith::theorem(&mut f, &p, name, 2, &|d, v| {
            let one = d.num(1);
            let a1 = d.add(v[0], one);
            let h = d.eq(a1, v[1]);
            let concl = d.le(v[0], v[1]);
            (vec![h], concl)
        })
        .expect("a + 1 = b gives a ≤ b");
        assert!(f.k.environment().contains(name));
    });
}

#[test]
fn a_negated_goal_is_proved_by_refutation() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let name = f.name("not_succ_le_self_by_linarith");
        let ty = linarith::theorem(&mut f, &p, name, 1, &|d, v| {
            let s = d.succ(v[0]);
            let inner = d.le(s, v[0]);
            let not_ = d.prelude().logic.not;
            let concl = d.const_app(not_, &[inner]);
            (vec![], concl)
        })
        .expect("¬(succ n ≤ n)");
        let expected = f.prelude_type(p.not_succ_le_self);
        assert!(
            f.k.def_eq(ty, expected),
            "the refutation route did not reach Nat.not_succ_le_self's statement",
        );
    });
}

#[test]
fn a_goal_needing_a_multiplier_of_two_is_proved() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let name = f.name("double_mono");
        linarith::theorem(&mut f, &p, name, 2, &|d, v| {
            let h = d.le(v[0], v[1]);
            let aa = d.add(v[0], v[0]);
            let bb = d.add(v[1], v[1]);
            let concl = d.le(aa, bb);
            (vec![h], concl)
        })
        .expect("a ≤ b gives a + a ≤ b + b");
        assert!(f.k.environment().contains(name));
    });
}
