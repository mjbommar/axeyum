//! Tests for the ℤ linear-arithmetic producer.
//!
//! The same four batteries as the ℕ suite, over a carrier where **nothing
//! reduces**: `Int.add` case-splits on both arguments, so every step the ℕ
//! normalizer got for free from ι-reduction is a lemma here. That makes the
//! corrupted-certificate battery even more load-bearing — a normalizer with no
//! definitional shortcuts has more places to be quietly wrong.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::int_prelude::ops::IntDev;
use crate::linarith::int as linarith;
use crate::linarith::{Certificate, Decline, LinForm};
use crate::{ExprId, IntPrelude, Kernel, NameId, NatOps, build_int_prelude, on_a_deep_stack};

/// A kernel carrying the integer prelude, plus a name root of this suite's own.
struct Env {
    k: Kernel,
    p: IntPrelude,
    root: NameId,
}

impl Env {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_int_prelude(&mut k).expect("Int prelude must build");
        let anon = k.anon();
        let root = k.name_str(anon, "linarith_int_test");
        Self { k, p, root }
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
fn retire(
    label: &str,
    mirror: fn(&IntPrelude) -> NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (Vec<ExprId>, ExprId),
) {
    let mut env = Env::new();
    let p = env.p;
    let expected = env.prelude_type(mirror(&p));
    let name = env.name(label);
    {
        let mut d = IntDev::new(&mut env.k, p);
        linarith::declare(&mut d, &p, name, arity, build)
            .unwrap_or_else(|e| panic!("{label}: the kernel refused the emitted term: {e:?}"));
    }
    let got = env.prelude_type(name);
    assert!(
        env.k.def_eq(got, expected),
        "{label}: the emitted declaration's type is not the prelude's statement",
    );
}

// ---------------------------------------------------------------------------
// 1. the five retirement targets
// ---------------------------------------------------------------------------

#[test]
fn target_add_left_comm() {
    on_a_deep_stack(|| {
        retire("add_left_comm", |p| p.add_left_comm, 3, &|d, v| {
            let (a, b, c) = (v[0], v[1], v[2]);
            let bc = d.iadd(b, c);
            let left = d.iadd(a, bc);
            let ac = d.iadd(a, c);
            let right = d.iadd(b, ac);
            (vec![], d.ieq(left, right))
        });
    });
}

#[test]
fn target_add_neg_cancel_left() {
    on_a_deep_stack(|| {
        retire(
            "add_neg_cancel_left",
            |p| p.add_neg_cancel_left,
            2,
            &|d, v| {
                // `a + ((-a) + b) = b` -- note the OUTER term is the positive `a`.
                let (a, b) = (v[0], v[1]);
                let neg_a = d.ineg(a);
                let inner = d.iadd(neg_a, b);
                let left = d.iadd(a, inner);
                (vec![], d.ieq(left, b))
            },
        );
    });
}

#[test]
fn target_add_neg_cancel_right() {
    on_a_deep_stack(|| {
        retire(
            "add_neg_cancel_right",
            |p| p.add_neg_cancel_right,
            2,
            &|d, v| {
                let (a, b) = (v[0], v[1]);
                let neg_b = d.ineg(b);
                let ab = d.iadd(a, b);
                let left = d.iadd(ab, neg_b);
                (vec![], d.ieq(left, a))
            },
        );
    });
}

#[test]
fn target_add_le_add_three() {
    on_a_deep_stack(|| {
        retire("add_le_add_three", |p| p.add_le_add_three, 6, &|d, v| {
            let (a, b, c, dd, e, f) = (v[0], v[1], v[2], v[3], v[4], v[5]);
            let h1 = d.ile(a, dd);
            let h2 = d.ile(b, e);
            let h3 = d.ile(c, f);
            let ab = d.iadd(a, b);
            let abc = d.iadd(ab, c);
            let de = d.iadd(dd, e);
            let def = d.iadd(de, f);
            (vec![h1, h2, h3], d.ile(abc, def))
        });
    });
}

#[test]
fn target_add_le_of_le_sub_left() {
    on_a_deep_stack(|| {
        retire(
            "add_le_of_le_sub_left",
            |p| p.add_le_of_le_sub_left,
            3,
            &|d, v| {
                let (a, b, c) = (v[0], v[1], v[2]);
                let c_sub_a = d.isub(c, a);
                let hyp = d.ile(b, c_sub_a);
                let ab = d.iadd(a, b);
                (vec![hyp], d.ile(ab, c))
            },
        );
    });
}

// ---------------------------------------------------------------------------
// 2. false goals decline
// ---------------------------------------------------------------------------

fn attempt(
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (Vec<ExprId>, ExprId),
) -> Result<ExprId, Decline> {
    let mut env = Env::new();
    let p = env.p;
    let mut d = IntDev::new(&mut env.k, p);
    let vars: Vec<ExprId> = (0..arity)
        .map(|_| {
            let fv = d.fresh_fvar();
            d.kernel().fvar(fv)
        })
        .collect();
    let (hyp_types, concl) = build(&mut d, &vars);
    let assumptions: Vec<linarith::Assumption> = hyp_types
        .iter()
        .map(|&ty| {
            let fv = d.fresh_fvar();
            let h = d.kernel().fvar(fv);
            (ty, h)
        })
        .collect();
    linarith::prove(&mut d, &p, &assumptions, concl)
}

#[test]
fn a_false_order_goal_declines() {
    on_a_deep_stack(|| {
        // `a + 1 ≤ a`.
        let got = attempt(1, &|d, v| {
            let one_nat = d.num(1);
            let one = d.of_nat(one_nat);
            let shifted = d.iadd(v[0], one);
            (vec![], d.ile(shifted, v[0]))
        });
        assert_eq!(got.err(), Some(Decline::NoCertificate));
    });
}

#[test]
fn a_false_goal_with_a_true_hypothesis_declines() {
    on_a_deep_stack(|| {
        let got = attempt(2, &|d, v| {
            let hyp = d.ile(v[0], v[1]);
            (vec![hyp], d.ile(v[1], v[0]))
        });
        assert_eq!(got.err(), Some(Decline::NoCertificate));
    });
}

#[test]
fn a_false_equality_goal_declines() {
    on_a_deep_stack(|| {
        // `a + 1 = a`.
        let got = attempt(1, &|d, v| {
            let one_nat = d.num(1);
            let one = d.of_nat(one_nat);
            let shifted = d.iadd(v[0], one);
            (vec![], d.ieq(shifted, v[0]))
        });
        assert_eq!(got.err(), Some(Decline::NoCertificate));
    });
}

// ---------------------------------------------------------------------------
// 3. corrupted certificates — the KERNEL must be the one that refuses
// ---------------------------------------------------------------------------

/// Set up `a ≤ b ⊢ a + c ≤ b + c`, hand `cert` to the emitter with the internal
/// arithmetic check disabled, and return what the kernel says.
fn kernel_verdict_on(cert: &Certificate, swap_hypothesis_proof: bool) -> Result<(), String> {
    let mut env = Env::new();
    let p = env.p;
    let name = env.name("corrupted");
    let mut d = IntDev::new(&mut env.k, p);
    let int_ty = d.int_ty();
    let a_fv = d.fresh_fvar();
    let b_fv = d.fresh_fvar();
    let c_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b = d.kernel().fvar(b_fv);
    let c = d.kernel().fvar(c_fv);
    let hyp_ty = d.ile(a, b);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    // The swap supplies a proof of a DIFFERENT true fact under a type saying
    // `a ≤ b`: `le_refl a : a ≤ a`.
    let proof = if swap_hypothesis_proof {
        d.const_app(p.le_refl, &[a])
    } else {
        h
    };
    let ac = d.iadd(a, c);
    let bc = d.iadd(b, c);
    let term = linarith::emit_le_from_certificate(
        &mut d,
        &p,
        &[(hyp_ty, proof)],
        ac,
        bc,
        cert,
        /* verify */ false,
    )
    .map_err(|e| format!("the procedure declined instead of emitting: {e:?}"))?;

    let concl = d.ile(ac, bc);
    let mut ty = d.arrow(hyp_ty, concl);
    let mut value = d.lam_fv(h_fv, hyp_ty, term);
    for fv in [c_fv, b_fv, a_fv] {
        ty = d.pi_fv(fv, int_ty, ty);
        value = d.lam_fv(fv, int_ty, value);
    }
    d.declare_theorem(name, ty, value)
        .map_err(|e| format!("{e:?}"))
}

/// The honest certificate: one copy of the hypothesis, no slack.
fn honest_certificate() -> Certificate {
    Certificate {
        multipliers: vec![1],
        residual: LinForm::zero(),
    }
}

#[test]
fn the_honest_certificate_is_the_positive_control() {
    on_a_deep_stack(|| {
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
        assert!(
            kernel_verdict_on(&cert, false).is_err(),
            "the kernel admitted a multiplier-2 certificate for a goal needing one copy",
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
        assert!(
            kernel_verdict_on(&cert, false).is_err(),
            "the kernel admitted a term whose slack was one larger than the identity allows",
        );
    });
}

#[test]
fn a_swapped_hypothesis_proof_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        assert!(
            kernel_verdict_on(&honest_certificate(), true).is_err(),
            "the kernel admitted a term whose hypothesis slot carried a proof of a \
             different proposition",
        );
    });
}

#[test]
fn the_procedures_own_check_also_catches_a_corrupted_certificate() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let mut d = IntDev::new(&mut env.k, p);
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let c_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);
        let c = d.kernel().fvar(c_fv);
        let hyp_ty = d.ile(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ac = d.iadd(a, c);
        let bc = d.iadd(b, c);
        let cert = Certificate {
            multipliers: vec![2],
            residual: LinForm::zero(),
        };
        let got =
            linarith::emit_le_from_certificate(&mut d, &p, &[(hyp_ty, h)], ac, bc, &cert, true);
        assert_eq!(got.err(), Some(Decline::NoCertificate));
    });
}

// ---------------------------------------------------------------------------
// 4. the fragment's boundary
// ---------------------------------------------------------------------------

#[test]
fn a_product_is_an_opaque_atom_even_at_a_numeral_multiplier() {
    on_a_deep_stack(|| {
        // `a * 2 ≤ a + a` is TRUE, and this fragment cannot see it: `Int.mul`
        // case-splits on both arguments, so `a * 2` does not unroll the way
        // `Nat.mul a 2` does. It is abstracted to an atom, and an atom tells
        // the search nothing. Measured, not asserted -- if `Int.mul` ever gains
        // an unrolling route this test is what says the boundary moved.
        let got = attempt(1, &|d, v| {
            let two_nat = d.num(2);
            let two = d.of_nat(two_nat);
            let doubled = d.imul(v[0], two);
            let sum = d.iadd(v[0], v[0]);
            (vec![], d.ile(doubled, sum))
        });
        assert_eq!(got.err(), Some(Decline::NoCertificate));
    });
}

#[test]
fn the_same_shape_without_the_product_is_proved() {
    on_a_deep_stack(|| {
        // The positive control for the decline above. Without it, "declines"
        // cannot be told from "the parser is broken".
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("self_add_self_le_self_add_self");
        let mut d = IntDev::new(&mut env.k, p);
        linarith::declare(&mut d, &p, name, 1, &|d, v| {
            let sum = d.iadd(v[0], v[0]);
            (vec![], d.ile(sum, sum))
        })
        .expect("a + a ≤ a + a is in the fragment");
        assert!(env.k.environment().contains(name));
    });
}

#[test]
fn a_product_atom_is_still_usable_as_an_unknown() {
    on_a_deep_stack(|| {
        // Abstracting a product is SOUND, not merely a gap: the atom denotes
        // some integer, and order facts about it still compose.
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("mul_atom_mono");
        let mut d = IntDev::new(&mut env.k, p);
        linarith::declare(&mut d, &p, name, 3, &|d, v| {
            let prod = d.imul(v[0], v[1]);
            let hyp = d.ile(prod, v[2]);
            let shifted = d.iadd(prod, v[0]);
            let bound = d.iadd(v[2], v[0]);
            (vec![hyp], d.ile(shifted, bound))
        })
        .expect("a*b ≤ c gives a*b + a ≤ c + a with a*b an atom");
        assert!(env.k.environment().contains(name));
    });
}

// ---------------------------------------------------------------------------
// the shapes the five targets do not exercise
// ---------------------------------------------------------------------------

#[test]
fn a_strict_goal_is_proved_through_lt_of_nat_add() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("lt_add_two");
        let mut d = IntDev::new(&mut env.k, p);
        linarith::declare(&mut d, &p, name, 1, &|d, v| {
            let two_nat = d.num(2);
            let two = d.of_nat(two_nat);
            let shifted = d.iadd(v[0], two);
            (vec![], d.ilt(v[0], shifted))
        })
        .expect("a < a + 2");
        assert!(env.k.environment().contains(name));
    });
}

#[test]
fn a_negated_goal_is_proved_by_refutation() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("not_add_one_le_self");
        let mut d = IntDev::new(&mut env.k, p);
        linarith::declare(&mut d, &p, name, 1, &|d, v| {
            let one_nat = d.num(1);
            let one = d.of_nat(one_nat);
            let shifted = d.iadd(v[0], one);
            let inner = d.ile(shifted, v[0]);
            (vec![], d.not(inner))
        })
        .expect("¬(a + 1 ≤ a)");
        assert!(env.k.environment().contains(name));
    });
}

#[test]
fn a_strict_hypothesis_keeps_its_strictness() {
    on_a_deep_stack(|| {
        // `a < b` gives both `a ≤ b` (weakened, via `le_of_lt` inside
        // `le_succ_of_lt`'s own proof) and the full `a + 1 ≤ b` — the fragment
        // edge ADR-1576 recorded as declined is now closed by
        // `Int.le_succ_of_lt`. Declared through the kernel, not merely
        // emitted: an `Ok` `ExprId` is not itself a claim of well-typedness.
        let weakened = attempt(2, &|d, v| {
            let hyp = d.ilt(v[0], v[1]);
            (vec![hyp], d.ile(v[0], v[1]))
        });
        assert!(weakened.is_ok(), "a < b must still give a ≤ b");

        let mut env = Env::new();
        let p = env.p;
        let name = env.name("strict_hyp_plus_one");
        let mut d = IntDev::new(&mut env.k, p);
        linarith::declare(&mut d, &p, name, 2, &|d, v| {
            let hyp = d.ilt(v[0], v[1]);
            let one_nat = d.num(1);
            let one = d.of_nat(one_nat);
            let shifted = d.iadd(v[0], one);
            (vec![hyp], d.ile(shifted, v[1]))
        })
        .expect("a < b must now give a + 1 ≤ b via Int.le_succ_of_lt");
        assert!(env.k.environment().contains(name));
    });
}
