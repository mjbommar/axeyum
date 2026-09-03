//! Tests for the `decide` producer.
//!
//! Four batteries:
//!
//! 1. **Ten closed goals accepted.** Each is pushed all the way through
//!    `Kernel::add_declaration` — not just `Kernel::infer` — so the
//!    assertion is "the kernel accepts this declaration", matching every
//!    other producer's own test convention.
//! 2. **Three goals with a free variable decline `NotClosed`.**
//! 3. **One goal whose reduction exceeds the fuel bound declines
//!    `Undecidable`, and does not hang** — the term is already in normal
//!    form (`d.num` builds a `succ`-chain directly), so a hang here would
//!    have to come from the producer's own peeling loop, not from kernel
//!    reduction; the test's own wall-clock bound is what rules that out.
//! 4. **Two corrupted terms are rejected by the KERNEL.** `decide` has no
//!    "verify" toggle to disable (unlike `linarith`/`ring`/`simp`, it has no
//!    internal check *to* disable — every term it emits is built directly
//!    from a value it already computed) — so these two tests instead build,
//!    BY HAND, the two term shapes `decide` emits (`Eq.refl` and a
//!    `le_step` chain) for a goal they do NOT actually prove, and require
//!    the kernel — not `decide` — to catch the mismatch.

#![allow(clippy::many_single_char_names)]

use crate::decide::{self, Decline};
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
        let root = k.name_str(anon, "decide_test");
        Self { k, p, st, root }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }
}

/// Run `decide` on `goal`, require `Ok`, and require the KERNEL to accept a
/// fresh `theorem <tag> : goal := <term>` declaration built from it.
fn accept(tag: &str, goal_of: &dyn Fn(&mut Fixture) -> ExprId) {
    let mut f = Fixture::new();
    let p = f.p;
    let goal = goal_of(&mut f);
    let term = decide::run(&mut f, &p, goal).unwrap_or_else(|e| panic!("{tag}: declined: {e:?}"));
    let name = f.name(tag);
    f.declare_theorem(name, goal, term)
        .unwrap_or_else(|e| panic!("{tag}: kernel rejected the emitted term: {e:?}"));
}

// ---------------------------------------------------------------------------
// 1. ten closed goals accepted
// ---------------------------------------------------------------------------

#[test]
fn eq_nat_zero_zero() {
    on_a_deep_stack(|| {
        accept("eq_nat_zero_zero", &|f| {
            let z = f.zero();
            f.eq(z, z)
        });
    });
}

#[test]
fn eq_nat_three_equals_add_one_two() {
    on_a_deep_stack(|| {
        accept("eq_nat_add", &|f| {
            let one = f.num(1);
            let two = f.num(2);
            let three = f.num(3);
            let sum = f.add(one, two);
            f.eq(sum, three)
        });
    });
}

#[test]
fn eq_nat_mul() {
    on_a_deep_stack(|| {
        accept("eq_nat_mul", &|f| {
            let three = f.num(3);
            let four = f.num(4);
            let twelve = f.num(12);
            let prod = f.mul(three, four);
            f.eq(prod, twelve)
        });
    });
}

#[test]
fn eq_bool_true_true() {
    on_a_deep_stack(|| {
        accept("eq_bool_true_true", &|f| {
            let t = f.bool_true();
            f.bool_eq(t, t)
        });
    });
}

#[test]
fn eq_bool_beq_agrees() {
    on_a_deep_stack(|| {
        accept("eq_bool_beq", &|f| {
            let five = f.num(5);
            let beq = f.beq(five, five);
            let t = f.bool_true();
            f.bool_eq(beq, t)
        });
    });
}

#[test]
fn le_refl_case() {
    on_a_deep_stack(|| {
        accept("le_refl_case", &|f| {
            let seven = f.num(7);
            f.le(seven, seven)
        });
    });
}

#[test]
fn le_strict_case() {
    on_a_deep_stack(|| {
        accept("le_strict_case", &|f| {
            let two = f.num(2);
            let nine = f.num(9);
            f.le(two, nine)
        });
    });
}

#[test]
fn le_from_computed_terms() {
    on_a_deep_stack(|| {
        accept("le_computed", &|f| {
            let two = f.num(2);
            let three = f.num(3);
            let six = f.mul(two, three);
            let ten = f.num(10);
            f.le(six, ten)
        });
    });
}

#[test]
fn lt_case() {
    on_a_deep_stack(|| {
        accept("lt_case", &|f| {
            let four = f.num(4);
            let five = f.num(5);
            f.lt(four, five)
        });
    });
}

#[test]
fn lt_from_computed_terms() {
    on_a_deep_stack(|| {
        accept("lt_computed", &|f| {
            let three = f.num(3);
            let one = f.num(1);
            let sum = f.add(three, one);
            let ten = f.num(10);
            f.lt(sum, ten)
        });
    });
}

// ---------------------------------------------------------------------------
// 2. three free-variable goals decline `NotClosed`
// ---------------------------------------------------------------------------

#[test]
fn free_variable_in_eq_declines_not_closed() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let goal = f.eq(n, n);
        assert_eq!(decide::run(&mut f, &p, goal), Err(Decline::NotClosed));
    });
}

#[test]
fn free_variable_in_le_declines_not_closed() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let five = f.num(5);
        let goal = f.le(n, five);
        assert_eq!(decide::run(&mut f, &p, goal), Err(Decline::NotClosed));
    });
}

#[test]
fn free_variable_buried_in_a_subterm_declines_not_closed() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let one = f.num(1);
        let buried = f.add(one, n);
        let two = f.num(2);
        let goal = f.eq(buried, two);
        assert_eq!(decide::run(&mut f, &p, goal), Err(Decline::NotClosed));
    });
}

// ---------------------------------------------------------------------------
// 3. exceeding the fuel bound declines, and does not hang
// ---------------------------------------------------------------------------

#[test]
fn a_magnitude_above_the_bound_declines_undecidable_not_a_hang() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        // Already in normal form -- `d.num` builds the `succ`-chain
        // directly, so this exercises the producer's OWN counting loop,
        // not kernel reduction.
        let big = f.num(decide::MAX_MAGNITUDE + 10);
        let goal = f.eq(big, big);
        assert_eq!(decide::run(&mut f, &p, goal), Err(Decline::Undecidable));
    });
}

// ---------------------------------------------------------------------------
// 4. two corrupted terms are rejected by the KERNEL
// ---------------------------------------------------------------------------

#[test]
fn a_false_eq_refl_claim_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let three = f.num(3);
        let four = f.num(4);
        // `decide` would never build this itself (it checks `lv == rv`
        // first) -- this is exactly the shape it WOULD emit if that check
        // were skipped, handed straight to the kernel.
        let term = f.refl(three);
        let goal = f.eq(three, four);
        let name = f.name("false_refl");
        let verdict = f.declare_theorem(name, goal, term);
        assert!(verdict.is_err(), "the kernel admitted `Eq.refl 3 : Eq 3 4`");
    });
}

#[test]
fn a_short_le_step_chain_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        // A `le_step` chain claiming `2 <= 4` built with only ONE step
        // (reaches 3, not 4) -- the shape `decide::le_witness` emits, with
        // the step count wrong.
        let two = f.num(2);
        let refl = f.lemma(p.le_refl, &[two]);
        let term = f.lemma(p.le_step, &[two, two, refl]); // : Le 2 3
        let four = f.num(4);
        let goal = f.le(two, four);
        let name = f.name("short_le_step");
        let verdict = f.declare_theorem(name, goal, term);
        assert!(
            verdict.is_err(),
            "the kernel admitted a `Le 2 3` term at type `Le 2 4`",
        );
    });
}
