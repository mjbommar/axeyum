//! Statement checks for `nat_prelude::stirling_lemmas`.
//!
//! A separate file from `stirling_tests.rs` for the merge hazard that file
//! records: two lanes adding items to one Rust file produce a conflict git
//! cuts mid-item.
//!
//! `stirling_tests.rs` checks the two **definitions** compute the right
//! triangle. This file checks the ten **theorems** are the right
//! propositions, which the kernel cannot do for us — it re-checked every
//! proof term at `add_declaration`, and
//! `nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free` reads
//! each name's kind and axiom footprint from the ENVIRONMENT, but a
//! well-typed theorem can still say the wrong thing.
//!
//! Two kinds of check, deliberately, because they fail on disjoint defects:
//!
//! - **symbolic**, at a genuinely free variable in a `LocalContext`. Nothing
//!   reduces there, so the inferred type is compared against an
//!   independently built expectation as a *statement*. This is what catches a
//!   transposed operand or a wrong index.
//! - **concrete**, at hand-computed instances from `stirling_tests.rs`'s
//!   table. Numerals reduce, which is what makes a wrong arithmetic claim
//!   visible — and what makes a symbolic-only suite blind to it.
//!
//! # Every negative control here discriminates, and that was checked
//!
//! The hazard `CLAUDE.md` records is a control that cannot fail. Two of the
//! obvious ones for this family are exactly that, and are NOT used:
//!
//! - `stirlingFirst_self` versus `stirlingSecond_self`: both triangles have
//!   `1` on the diagonal, so swapping the kinds discriminates nothing. The
//!   control used instead is the off-diagonal `c(4,3) = 6 ≠ 1`, which rules
//!   out a proof that dropped the diagonal condition.
//! - `stirlingFirst_succ_self_left` versus its second-kind analogue: both are
//!   `choose (n+1) 2` in Mathlib, and both are `6` at `n = 3`. The controls
//!   used instead move the index on each side independently
//!   (`choose 3 2 = 3` and `c(3,2) = 3`, against the true `6`).
//!
//! Where the two kinds DO separate, the cross-kind control is used, because
//! it is the strongest available: column 1 is `n!` for the first kind and all
//! ones for the second, so `c(4,1) = 6` against `S(4,1) = 1`.
//!
//! **A third vacuous control was written here and CAUGHT BY THE SUITE**, not
//! by review, and it is worth recording because it is not the shape the
//! warning above predicts. The obvious control for `stirlingFirst_zero_succ`
//! is the transposed index `stirlingFirst (k+1) 0 = 0` — a different-looking
//! proposition, both indices free of numerals, apparently safe. It is not:
//! `stirlingFirst 0 (succ k)` reduces through the ZERO row's inner recursor
//! at a `succ` scrutinee, and `stirlingFirst (succ k) 0` reduces through the
//! SUCC row's inner recursor at a literal `0` — **both land on the literal
//! `0` even at a free `k`**, so the two statements are one statement up to
//! defeq and nothing could distinguish them.
//!
//! Going symbolic is what usually rescues a control (it is what rescued the
//! min/max lane's `max 7 2`), and here it does not, because the reduction
//! that collapses the distinction is driven by the CONSTRUCTOR shapes rather
//! than by any numeral. The controls used instead drop the `succ` —
//! `stirlingFirst 0 k = 0` and `stirlingFirst n 0 = 0`, each false at `0` and
//! each STUCK at a free variable — and the suite additionally asserts the
//! counterexample (`stirlingFirst 0 0 = 1`), so a control that stopped
//! discriminating would fail rather than pass quietly.

use crate::expr::ExprId;
use crate::{
    BinderInfo, Kernel, LocalContext, LocalDecl, NatOps, NatPrelude, NatState, build_nat_prelude,
};

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

    /// One free `Nat` variable in a `LocalContext` that `infer_in` can read.
    fn free_nat(&mut self, ctx: &mut LocalContext) -> ExprId {
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let fv = self.fresh_fvar();
        let x = self.k.fvar(fv);
        ctx.push(LocalDecl {
            fvar: fv,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
        x
    }

    fn first(&mut self, n: ExprId, k: ExprId) -> ExprId {
        let name = self.p.stirling_first;
        self.const_app(name, &[n, k])
    }

    fn second(&mut self, n: ExprId, k: ExprId) -> ExprId {
        let name = self.p.stirling_second;
        self.const_app(name, &[n, k])
    }
}

/// The four defining equations, at a free variable. Each is `Eq.refl` in the
/// module, so the only thing worth checking is that the equation stated is
/// Mathlib's — in particular that the `succ` row's column zero is `0` (where
/// `choose`'s is `1`) and that the coefficient sits on the `k + 1` call.
#[test]
fn the_four_defining_equations_state_mathlibs_recurrence() {
    let mut f = Fixture::new();
    let p = f.p;

    // stirlingFirst_zero : stirlingFirst 0 0 = 1
    let proof = f.k.const_(p.stirling_first_zero, vec![]);
    let inferred =
        f.k.infer(proof)
            .expect("stirlingFirst_zero must type-check");
    let zero = f.zero();
    let lhs = f.first(zero, zero);
    let one = f.num(1);
    let expected = f.eq(lhs, one);
    assert!(
        f.k.def_eq(inferred, expected),
        "stirlingFirst_zero must state stirlingFirst 0 0 = 1"
    );
    let zero2 = f.zero();
    let wrong = f.eq(lhs, zero2);
    assert!(
        !f.k.def_eq(inferred, wrong),
        "negative control: stirlingFirst_zero must NOT state ... = 0"
    );

    // stirlingFirst_zero_succ : ∀ k, stirlingFirst 0 (succ k) = 0
    let mut ctx = LocalContext::new();
    let k_free = f.free_nat(&mut ctx);
    let proof = f.lemma(p.stirling_first_zero_succ, &[k_free]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("stirlingFirst_zero_succ must type-check");
    let zero = f.zero();
    let sk = f.succ(k_free);
    let lhs = f.first(zero, sk);
    let zero2 = f.zero();
    let expected = f.eq(lhs, zero2);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "stirlingFirst_zero_succ must state stirlingFirst 0 (k+1) = 0"
    );
    // NOT the transposed index `stirlingFirst (k+1) 0`: see this file's doc.
    // Both reduce to the literal `0` even at a free `k`, so that control is
    // VACUOUS -- the two propositions are one proposition up to defeq.
    //
    // What discriminates is dropping the `succ`: `stirlingFirst 0 k = 0` is
    // FALSE at k = 0, and at a free `k` the inner recursor is stuck, so it is
    // a genuinely different term.
    let lhs_unguarded = f.first(zero, k_free);
    let zero3 = f.zero();
    let unguarded = f.eq(lhs_unguarded, zero3);
    assert!(
        !f.k.def_eq_in(inferred, unguarded, &mut ctx),
        "negative control: the column must be a SUCCESSOR -- \
         stirlingFirst 0 0 is 1, so the unguarded form is false"
    );
    // ...and confirm that control is not vacuous the other way: the unguarded
    // form really does fail at k = 0.
    let at_0_0 = f.first(zero, zero);
    let one2 = f.num(1);
    assert!(
        f.k.def_eq(at_0_0, one2),
        "the control's counterexample must be real: stirlingFirst 0 0 = 1"
    );

    // stirlingFirst_succ_zero : ∀ n, stirlingFirst (succ n) 0 = 0
    let mut ctx = LocalContext::new();
    let n_free = f.free_nat(&mut ctx);
    let proof = f.lemma(p.stirling_first_succ_zero, &[n_free]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("stirlingFirst_succ_zero must type-check");
    let sn = f.succ(n_free);
    let zero = f.zero();
    let lhs = f.first(sn, zero);
    let zero2 = f.zero();
    let expected = f.eq(lhs, zero2);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "stirlingFirst_succ_zero must state stirlingFirst (n+1) 0 = 0"
    );
    // The `choose`-shaped mistake this whole family exists to avoid.
    let one = f.num(1);
    let wrong = f.eq(lhs, one);
    assert!(
        !f.k.def_eq_in(inferred, wrong, &mut ctx),
        "negative control: stirlingFirst (n+1) 0 is 0, NOT 1 -- 1 is what \
         choose (n+1) 0 gives"
    );
    // And the row must be a SUCCESSOR: `stirlingFirst n 0 = 0` is false at
    // n = 0, and at a free `n` the outer recursor is stuck.
    let lhs_unguarded = f.first(n_free, zero);
    let zero3 = f.zero();
    let unguarded = f.eq(lhs_unguarded, zero3);
    assert!(
        !f.k.def_eq_in(inferred, unguarded, &mut ctx),
        "negative control: the row must be a SUCCESSOR -- stirlingFirst 0 0 \
         is 1, so the unguarded form is false"
    );

    // stirlingFirst_succ_succ : ∀ n k,
    //   stirlingFirst (n+1) (k+1) = n * stirlingFirst n (k+1) + stirlingFirst n k
    let mut ctx = LocalContext::new();
    let n_free = f.free_nat(&mut ctx);
    let k_free = f.free_nat(&mut ctx);
    let proof = f.lemma(p.stirling_first_succ_succ, &[n_free, k_free]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("stirlingFirst_succ_succ must type-check");
    let sn = f.succ(n_free);
    let sk = f.succ(k_free);
    let lhs = f.first(sn, sk);
    let at_sk = f.first(n_free, sk);
    let at_k = f.first(n_free, k_free);
    let scaled = f.mul(n_free, at_sk);
    let rhs = f.add(scaled, at_k);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "stirlingFirst_succ_succ must state Mathlib's recurrence"
    );
    // Coefficient on the WRONG recursive call.
    let scaled_wrong = f.mul(n_free, at_k);
    let rhs_wrong = f.add(scaled_wrong, at_sk);
    let wrong = f.eq(lhs, rhs_wrong);
    assert!(
        !f.k.def_eq_in(inferred, wrong, &mut ctx),
        "negative control: the coefficient multiplies the (k+1) call, not the \
         k call"
    );
    // The SECOND kind's coefficient in the first kind's equation.
    let scaled_second = f.mul(sk, at_sk);
    let rhs_second = f.add(scaled_second, at_k);
    let wrong = f.eq(lhs, rhs_second);
    assert!(
        !f.k.def_eq_in(inferred, wrong, &mut ctx),
        "negative control: the first kind's coefficient is the ROW index n, \
         not the column index k+1"
    );
}

/// `stirlingFirst_succ_succ` at the instance the definition tests use, where
/// the arithmetic is checkable by hand: `c(4,2) = 3*c(3,2) + c(3,1) =
/// 3*3 + 2 = 11`. The symbolic check above cannot see a wrong VALUE, only a
/// wrong shape; this cannot see a wrong shape, only a wrong value.
#[test]
fn the_recurrence_computes_the_hand_checked_entry() {
    let mut f = Fixture::new();
    let p = f.p;
    let three = f.num(3);
    let one = f.num(1);

    let proof = f.lemma(p.stirling_first_succ_succ, &[three, one]);
    let inferred = f.k.infer(proof).expect("must type-check at (3,1)");
    let four = f.num(4);
    let two = f.num(2);
    let lhs = f.first(four, two);
    let eleven = f.num(11);
    let expected = f.eq(lhs, eleven);
    assert!(
        f.k.def_eq(inferred, expected),
        "stirlingFirst_succ_succ at (3,1) must reduce to 11 = 11"
    );
    // 3*c(3,1) + c(3,2) = 3*2 + 3 = 9, the transposed-coefficient triangle.
    let nine = f.num(9);
    let wrong = f.eq(lhs, nine);
    assert!(
        !f.k.def_eq(inferred, wrong),
        "negative control: 9 is what the transposed coefficient gives"
    );
    // 2*c(3,2) + c(3,1) = 2*3 + 2 = 8, the second kind's coefficient.
    let eight = f.num(8);
    let wrong = f.eq(lhs, eight);
    assert!(
        !f.k.def_eq(inferred, wrong),
        "negative control: 8 is what the second kind's coefficient gives"
    );
}

/// Both `eq_zero_of_lt` mirrors, symbolically (the statement) and concretely
/// (that the hypothesis is doing work).
#[test]
fn eq_zero_of_lt_states_the_conditional_and_the_condition_is_load_bearing() {
    let mut f = Fixture::new();
    let p = f.p;

    for (theorem, is_first) in [
        (p.stirling_first_eq_zero_of_lt, true),
        (p.stirling_second_eq_zero_of_lt, false),
    ] {
        // Symbolic: ∀ n k, Lt n k → stirling n k = 0.
        let mut ctx = LocalContext::new();
        let n_free = f.free_nat(&mut ctx);
        let k_free = f.free_nat(&mut ctx);
        let hyp_ty = f.lt(n_free, k_free);
        let anon = f.anon_name();
        let h_fv = f.fresh_fvar();
        let h = f.k.fvar(h_fv);
        ctx.push(LocalDecl {
            fvar: h_fv,
            name: anon,
            ty: hyp_ty,
            info: BinderInfo::Default,
        });
        let proof = f.lemma(theorem, &[n_free, k_free, h]);
        let inferred =
            f.k.infer_in(proof, &mut ctx)
                .expect("eq_zero_of_lt must type-check at a free (n, k)");
        let lhs = if is_first {
            f.first(n_free, k_free)
        } else {
            f.second(n_free, k_free)
        };
        let zero = f.zero();
        let expected = f.eq(lhs, zero);
        assert!(
            f.k.def_eq_in(inferred, expected, &mut ctx),
            "eq_zero_of_lt must conclude stirling n k = 0"
        );
        // The transposed conclusion: `stirling k n`, which under `n < k` is
        // the sub-diagonal entry and generally NOT zero.
        let lhs_transposed = if is_first {
            f.first(k_free, n_free)
        } else {
            f.second(k_free, n_free)
        };
        let zero2 = f.zero();
        let transposed = f.eq(lhs_transposed, zero2);
        assert!(
            !f.k.def_eq_in(inferred, transposed, &mut ctx),
            "negative control: the conclusion is about stirling n k, not \
             stirling k n"
        );

        // Concrete, above the diagonal: c(2,3) = S(2,3) = 0, which the
        // theorem gives, and where its hypothesis 2 < 3 holds.
        let two = f.num(2);
        let three = f.num(3);
        let above = if is_first {
            f.first(two, three)
        } else {
            f.second(two, three)
        };
        let zero3 = f.zero();
        assert!(
            f.k.def_eq(above, zero3),
            "the entry the theorem is about must really be 0"
        );
        // Concrete, BELOW the diagonal, where the hypothesis fails: c(3,2) =
        // S(3,2) = 3. So an unconditional version of this theorem would be
        // false, which is what makes `Lt n k` load-bearing rather than
        // decorative.
        let below = if is_first {
            f.first(three, two)
        } else {
            f.second(three, two)
        };
        let zero4 = f.zero();
        assert!(
            !f.k.def_eq(below, zero4),
            "negative control: stirling 3 2 is 3, not 0 -- dropping the \
             Lt hypothesis would make this theorem false"
        );
    }
}

/// `stirlingFirst_self`, and the off-diagonal control that discriminates
/// (the cross-kind one does not: both diagonals are all ones).
#[test]
fn stirling_first_self_states_the_diagonal_is_one() {
    let mut f = Fixture::new();
    let p = f.p;

    let mut ctx = LocalContext::new();
    let n_free = f.free_nat(&mut ctx);
    let proof = f.lemma(p.stirling_first_self, &[n_free]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("stirlingFirst_self must type-check at a free n");
    let lhs = f.first(n_free, n_free);
    let one = f.num(1);
    let expected = f.eq(lhs, one);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "stirlingFirst_self must state stirlingFirst n n = 1"
    );
    // Off by one in the column: `stirlingFirst n (n+1)` is 0, not 1.
    let sn = f.succ(n_free);
    let off = f.first(n_free, sn);
    let one2 = f.num(1);
    let wrong = f.eq(off, one2);
    assert!(
        !f.k.def_eq_in(inferred, wrong, &mut ctx),
        "negative control: the diagonal, not the column one to its right"
    );

    // Concrete, and the control is the off-diagonal rather than the other
    // kind: c(4,4) = 1 while c(4,3) = 6.
    let four = f.num(4);
    let three = f.num(3);
    let diagonal = f.first(four, four);
    let one3 = f.num(1);
    assert!(f.k.def_eq(diagonal, one3), "c(4,4) must be 1");
    let sub = f.first(four, three);
    let one4 = f.num(1);
    assert!(
        !f.k.def_eq(sub, one4),
        "negative control: c(4,3) is 6, so `= 1` is a claim about the \
         diagonal specifically"
    );
}

/// The two column-one mirrors, which are where the triangles separate:
/// `c(n+1,1) = n!` against `S(n+1,1) = 1`. Each theorem's cross-kind control
/// is therefore a genuine discriminator, unlike the diagonal's.
#[test]
fn the_column_one_mirrors_separate_the_two_kinds() {
    let mut f = Fixture::new();
    let p = f.p;

    // stirlingFirst_one_right : ∀ n, stirlingFirst (n+1) 1 = n!
    let mut ctx = LocalContext::new();
    let n_free = f.free_nat(&mut ctx);
    let proof = f.lemma(p.stirling_first_one_right, &[n_free]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("stirlingFirst_one_right must type-check at a free n");
    let sn = f.succ(n_free);
    let one = f.num(1);
    let lhs = f.first(sn, one);
    let rhs = f.factorial(n_free);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "stirlingFirst_one_right must state stirlingFirst (n+1) 1 = n!"
    );
    // Off by one on the factorial: `(n+1)!`, the natural mis-statement.
    let rhs_wrong = f.factorial(sn);
    let wrong = f.eq(lhs, rhs_wrong);
    assert!(
        !f.k.def_eq_in(inferred, wrong, &mut ctx),
        "negative control: the right-hand side is n!, not (n+1)!"
    );

    // stirlingSecond_one_right : ∀ n, stirlingSecond (n+1) 1 = 1
    let mut ctx = LocalContext::new();
    let n_free = f.free_nat(&mut ctx);
    let proof = f.lemma(p.stirling_second_one_right, &[n_free]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("stirlingSecond_one_right must type-check at a free n");
    let sn = f.succ(n_free);
    let one = f.num(1);
    let lhs = f.second(sn, one);
    let one2 = f.num(1);
    let expected = f.eq(lhs, one2);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "stirlingSecond_one_right must state stirlingSecond (n+1) 1 = 1"
    );
    // The first kind in the second kind's statement.
    let lhs_first = f.first(sn, one);
    let one3 = f.num(1);
    let wrong = f.eq(lhs_first, one3);
    assert!(
        !f.k.def_eq_in(inferred, wrong, &mut ctx),
        "negative control: this is the SECOND kind's column one"
    );

    // Concrete, at n = 3, where the two kinds disagree: c(4,1) = 6 = 3!,
    // S(4,1) = 1. Each is the other's discriminating control.
    let four = f.num(4);
    let one4 = f.num(1);
    let c41 = f.first(four, one4);
    let six = f.num(6);
    assert!(f.k.def_eq(c41, six), "c(4,1) must be 3! = 6");
    let one5 = f.num(1);
    assert!(
        !f.k.def_eq(c41, one5),
        "negative control: c(4,1) is 6, not 1 -- 1 is the second kind's value"
    );
    let one6 = f.num(1);
    let s41 = f.second(four, one6);
    let one7 = f.num(1);
    assert!(f.k.def_eq(s41, one7), "S(4,1) must be 1");
    let six2 = f.num(6);
    assert!(
        !f.k.def_eq(s41, six2),
        "negative control: S(4,1) is 1, not 6 -- 6 is the first kind's value"
    );
}

/// `stirlingFirst_succ_self_left : stirlingFirst (n+1) n = choose (n+1) 2`.
///
/// The cross-kind control is vacuous here (Mathlib proves the same identity
/// for the second kind, and both are 6 at n = 3), so both controls move an
/// index instead — one on each side of the equation.
#[test]
fn stirling_first_succ_self_left_meets_pascals_rule() {
    let mut f = Fixture::new();
    let p = f.p;

    let mut ctx = LocalContext::new();
    let n_free = f.free_nat(&mut ctx);
    let proof = f.lemma(p.stirling_first_succ_self_left, &[n_free]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("stirlingFirst_succ_self_left must type-check at a free n");
    let sn = f.succ(n_free);
    let two = f.num(2);
    let lhs = f.first(sn, n_free);
    let rhs = f.choose(sn, two);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "stirlingFirst_succ_self_left must state \
         stirlingFirst (n+1) n = choose (n+1) 2"
    );
    // Index moved on the right: `choose n 2`.
    let two2 = f.num(2);
    let rhs_wrong = f.choose(n_free, two2);
    let wrong = f.eq(lhs, rhs_wrong);
    assert!(
        !f.k.def_eq_in(inferred, wrong, &mut ctx),
        "negative control: the binomial is at n+1, not n"
    );
    // Index moved on the left: `stirlingFirst n n`, i.e. the diagonal.
    let lhs_wrong = f.first(n_free, n_free);
    let two3 = f.num(2);
    let rhs2 = f.choose(sn, two3);
    let wrong = f.eq(lhs_wrong, rhs2);
    assert!(
        !f.k.def_eq_in(inferred, wrong, &mut ctx),
        "negative control: the left-hand side is the SUB-diagonal entry"
    );

    // Concrete at n = 3: c(4,3) = 6 = choose 4 2, and both moved indices are
    // genuinely different numbers (choose 3 2 = 3, c(3,3) = 1).
    let four = f.num(4);
    let three = f.num(3);
    let two4 = f.num(2);
    let c43 = f.first(four, three);
    let choose_4_2 = f.choose(four, two4);
    assert!(
        f.k.def_eq(c43, choose_4_2),
        "c(4,3) and choose 4 2 must both be 6"
    );
    let two5 = f.num(2);
    let choose_3_2 = f.choose(three, two5);
    assert!(
        !f.k.def_eq(c43, choose_3_2),
        "negative control: choose 3 2 is 3, not 6"
    );
    let c33 = f.first(three, three);
    assert!(
        !f.k.def_eq(c33, choose_4_2),
        "negative control: c(3,3) is 1, not 6"
    );
}
