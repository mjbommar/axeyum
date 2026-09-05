//! Evaluation tests and negative controls for `two_squares.rs`.
//!
//! `Int.IsSumOfTwoSquares` is a `Definition`, and **the trusted gate cannot
//! tell you a `Definition` is wrong** — it type-checks whatever `Prop` the
//! body happens to be (`CLAUDE.md`, "the declaration is rejected, or admitted
//! and wrong"). So nothing here asserts that the prelude built; every battery
//! settles what the declaration MEANS, by reduction at concrete arguments and
//! by comparison against a deliberately wrong variant, and each battery
//! asserts what must hold AND what must fail so no run can be vacuous.
//!
//! The magnitudes are deliberately tiny. `Nat` numerals here are unary and
//! cost is superlinear in the largest magnitude formed, so the worked
//! representations are `5 = 1² + 2²`, `13 = 2² + 3²` and `17 = 1² + 4²` — the
//! three primes the brief names, and the largest square formed anywhere in
//! this file is `4² = 16`.

use super::super::{Kernel, build_int_prelude};
use super::first_supplementary::pos_of_nat_succ;
use super::ops::IntDev;
use super::two_squares::{
    imodeq, inner_predicate, int_exists, is_sum_of_two_squares, ofnat_ne, outer_predicate,
};
use crate::NameId;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Int.ofNat k` for a small numeral.
fn int_num(d: &mut IntDev<'_>, k: u32) -> ExprId {
    let n = d.num(k);
    d.of_nat(n)
}

/// A fresh top-level name, so a probe theorem can be admitted without
/// colliding with the prelude's own namespace.
fn probe_name(d: &mut IntDev<'_>, label: &str) -> NameId {
    let anon = d.kernel().anon();
    let root = d.kernel().name_str(anon, "TwoSquaresProbe");
    d.kernel().name_str(root, label)
}

/// Try to admit `theorem <label> : IsSumOfTwoSquares (ofNat n) :=
/// Int.isSumOfTwoSquares_intro (ofNat n) (ofNat a) (ofNat b) rfl`.
///
/// Returns the verdict rather than asserting, so a caller can require BOTH
/// outcomes and no run can be vacuous: a `true` means the kernel accepted
/// `n = a² + b²` by its own reduction, a `false` that it refused it.
fn admits_representation(d: &mut IntDev<'_>, n: u32, a: u32, b: u32, label: &str) -> bool {
    let p = d.int();
    let ni = int_num(d, n);
    let ai = int_num(d, a);
    let bi = int_num(d, b);
    let refl = d.irefl(ni);
    let proof = d.const_app(p.is_sum_of_two_squares_intro, &[ni, ai, bi, refl]);
    let ty = is_sum_of_two_squares(d, ni);
    let name = probe_name(d, label);
    d.declare_theorem(name, ty, proof).is_ok()
}

/// `5 = 1² + 2²`, `13 = 2² + 3²`, `17 = 1² + 4²` — the kernel accepts each
/// through `Int.isSumOfTwoSquares_intro` with `Eq.refl` as the equation, i.e.
/// it computes the sum of squares itself.
#[test]
fn the_three_primes_are_witnessed_sums_of_two_squares() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    assert!(
        admits_representation(&mut d, 5, 1, 2, "five"),
        "5 = 1^2 + 2^2 must be admitted"
    );
    assert!(
        admits_representation(&mut d, 13, 2, 3, "thirteen"),
        "13 = 2^2 + 3^2 must be admitted"
    );
    assert!(
        admits_representation(&mut d, 17, 1, 4, "seventeen"),
        "17 = 1^2 + 4^2 must be admitted"
    );
}

/// The negative half of the same battery, which is what makes it a
/// measurement rather than a formality: a WRONG pair is refused.
///
/// `5 = 1² + 1²` and `13 = 2² + 2²` are false, and `3` is not a sum of two
/// squares at all (the mod-4 obstruction) so every small pair fails for it.
/// If `Int.IsSumOfTwoSquares` were, say, `n = a² · b²` or `n = a + b`, at
/// least one of these three would go through.
#[test]
fn wrong_pairs_are_refused_by_the_kernel() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    assert!(
        !admits_representation(&mut d, 5, 1, 1, "five_wrong"),
        "5 = 1^2 + 1^2 is false and must be refused"
    );
    assert!(
        !admits_representation(&mut d, 13, 2, 2, "thirteen_wrong"),
        "13 = 2^2 + 2^2 is false and must be refused"
    );
    assert!(
        !admits_representation(&mut d, 3, 1, 1, "three_wrong"),
        "3 = 1^2 + 1^2 is false and must be refused"
    );
}

/// `Int.IsSumOfTwoSquares n` unfolds to exactly `∃ a, ∃ b, n = a² + b²` —
/// and NOT to the transposed variant `∃ a, ∃ b, n = a·b + a·b`, which
/// type-checks identically and would be admitted identically.
///
/// This is the check the kernel cannot make for us: both bodies are `Prop`s
/// built from the same constants in the same shape, so only a `def_eq`
/// comparison against the intended term separates them.
#[test]
fn is_sum_of_two_squares_unfolds_to_the_intended_double_existential() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let int_ty = d.int_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let stated = is_sum_of_two_squares(&mut d, n);
    let intended = {
        let outer = outer_predicate(&mut d, n);
        int_exists(&mut d, outer)
    };
    assert!(
        d.kernel().def_eq(stated, intended),
        "Int.IsSumOfTwoSquares must unfold to the double existential over a^2 + b^2"
    );

    // The wrong variant: `a*b + a*b` in place of `a*a + b*b`.
    let transposed = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let inner = {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let ab = d.imul(a, b);
            let sum = d.iadd(ab, ab);
            let body = d.ieq(n, sum);
            d.lam_fv(b_fv, int_ty, body)
        };
        let body = int_exists(&mut d, inner);
        let outer = d.lam_fv(a_fv, int_ty, body);
        int_exists(&mut d, outer)
    };
    assert!(
        !d.kernel().def_eq(stated, transposed),
        "Int.IsSumOfTwoSquares must NOT be the a*b + a*b variant"
    );
}

/// The inner predicate really does fix the FIRST square: `inner_predicate n a`
/// applied at `b` is `n = a² + b²`, with the OUTER witness's square on the
/// left.
///
/// **This check has to run at free variables, not numerals.** The first draft
/// used `17 = 1² + 4²` and its swap `4² + 1²` — both reduce to `17`, so the
/// negative control was vacuous and fired on a term that was simply equal.
/// Sums of two squares are symmetric, so the ordering is observable only in
/// the TERM, which means the comparison must be symbolic.
#[test]
fn the_witness_slots_are_ordered_as_stated() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let pred = inner_predicate(&mut d, n, a);
    let at_b = d.apply(pred, &[b]);
    let expected = {
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let sum = d.iadd(aa, bb);
        d.ieq(n, sum)
    };
    assert!(
        d.kernel().def_eq(at_b, expected),
        "inner_predicate n a applied at b must be `n = a*a + b*b`"
    );
    let swapped = {
        let bb = d.imul(b, b);
        let aa = d.imul(a, a);
        let sum = d.iadd(bb, aa);
        d.ieq(n, sum)
    };
    assert!(
        !d.kernel().def_eq(at_b, swapped),
        "inner_predicate must place the OUTER witness's square first"
    );
    // A genuinely different proposition is rejected too, so the control above
    // is measuring the operand order and not merely `Int.add`'s lack of a
    // reduction rule at symbolic arguments.
    let product = {
        let ab = d.imul(a, b);
        d.ieq(n, ab)
    };
    assert!(
        !d.kernel().def_eq(at_b, product),
        "inner_predicate must not be the product `n = a*b`"
    );
}

/// The Brahmagupta–Fibonacci identity is checked at a concrete quadruple by
/// reduction — the ring producer emitted a term the kernel accepted, but that
/// only says the two SIDES AS STATED are equal; it says nothing about whether
/// the statement is the identity anyone wanted.
///
/// `(1²+2²)(1²+1²) = 5·2 = 10` and `(1·1−2·1)² + (1·1+2·1)² = 1 + 9 = 10`.
/// The negative control is the same quadruple against the CONJUGATE grouping
/// `(ac+bd)² + (ad−bc)² = 9 + 1`, which happens to be equal here, so the
/// control that actually discriminates is a THIRD, wrong grouping.
#[test]
fn brahmagupta_fibonacci_holds_at_a_concrete_quadruple() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let one = int_num(&mut d, 1);
    let two = int_num(&mut d, 2);

    // (1² + 2²)(1² + 1²)
    let lhs = {
        let a = d.imul(one, one);
        let b = d.imul(two, two);
        let left = d.iadd(a, b);
        let c = d.imul(one, one);
        let e = d.imul(one, one);
        let right = d.iadd(c, e);
        d.imul(left, right)
    };
    // (1·1 − 2·1)² + (1·1 + 2·1)²
    let rhs = {
        let ac = d.imul(one, one);
        let bd = d.imul(two, one);
        let u = d.isub(ac, bd);
        let ad = d.imul(one, one);
        let bc = d.imul(two, one);
        let w = d.iadd(ad, bc);
        let uu = d.imul(u, u);
        let ww = d.imul(w, w);
        d.iadd(uu, ww)
    };
    assert!(
        d.kernel().def_eq(lhs, rhs),
        "(1^2+2^2)(1^2+1^2) must reduce to (1-2)^2 + (1+2)^2 = 10"
    );

    // A wrong grouping: `(ac−bd)² + (ad−bc)²` = 1 + 1 = 2, not 10.
    let wrong = {
        let ac = d.imul(one, one);
        let bd = d.imul(two, one);
        let u = d.isub(ac, bd);
        let ad = d.imul(one, one);
        let bc = d.imul(two, one);
        let w = d.isub(ad, bc);
        let uu = d.imul(u, u);
        let ww = d.imul(w, w);
        d.iadd(uu, ww)
    };
    assert!(
        !d.kernel().def_eq(lhs, wrong),
        "the both-minus grouping is NOT the identity and must not reduce equal"
    );

    // And the theorem's own statement, instantiated at that quadruple, is
    // accepted by the kernel.
    let instance = d.const_app(p.brahmagupta_fibonacci, &[one, two, one, one]);
    let ty = d.ieq(lhs, rhs);
    let name = probe_name(&mut d, "bf_instance");
    assert!(
        d.declare_theorem(name, ty, instance).is_ok(),
        "Int.brahmaguptaFibonacci at (1,2,1,1) must check against 10 = 10"
    );
}

/// `Int.isSumOfTwoSquares_mul` composes two concrete witnesses: `5 · 13` is a
/// sum of two squares because `5` and `13` each are. Nothing is reduced here
/// (the product stays `Int.mul 5 13`), so the cost is one type application.
#[test]
fn the_composition_law_applies_to_two_concrete_witnesses() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let five = int_num(&mut d, 5);
    let thirteen = int_num(&mut d, 13);

    let h5 = {
        let a = int_num(&mut d, 1);
        let b = int_num(&mut d, 2);
        let refl = d.irefl(five);
        d.const_app(p.is_sum_of_two_squares_intro, &[five, a, b, refl])
    };
    let h13 = {
        let a = int_num(&mut d, 2);
        let b = int_num(&mut d, 3);
        let refl = d.irefl(thirteen);
        d.const_app(p.is_sum_of_two_squares_intro, &[thirteen, a, b, refl])
    };
    let proof = d.const_app(p.is_sum_of_two_squares_mul, &[five, thirteen, h5, h13]);
    let product = d.imul(five, thirteen);
    let ty = is_sum_of_two_squares(&mut d, product);
    let name = probe_name(&mut d, "five_times_thirteen");
    assert!(
        d.declare_theorem(name, ty, proof).is_ok(),
        "5*13 must be a sum of two squares by the composition law"
    );
}

/// Try to admit `theorem <label> : Not (IsSumOfTwoSquares (ofNat n)) :=
/// Int.not_isSumOfTwoSquares_of_modEq_four_three (ofNat n) rfl`.
///
/// The `rfl` is the whole measurement: `ModEq 4 n 3` unfolds to
/// `Eq Int (emod n 4) (emod 3 4)`, so `Eq.refl` checks exactly when the kernel
/// computes `n % 4 = 3` itself. Returns the verdict rather than asserting, so
/// a caller can require both outcomes.
fn admits_mod_four_refutation(d: &mut IntDev<'_>, n: u32, label: &str) -> bool {
    let p = d.int();
    let ni = int_num(d, n);
    let three = int_num(d, 3);
    let refl = d.irefl(three);
    let proof = d.const_app(
        p.not_is_sum_of_two_squares_of_mod_eq_four_three,
        &[ni, refl],
    );
    let sum = is_sum_of_two_squares(d, ni);
    let ty = d.not(sum);
    let name = probe_name(d, label);
    d.declare_theorem(name, ty, proof).is_ok()
}

/// `3`, `7` and `11` are each `3 (mod 4)` and therefore NOT sums of two
/// squares — and the kernel checks the congruence by its own reduction of
/// `Int.emod`, not from anything asserted here.
#[test]
fn three_seven_and_eleven_are_refuted_by_the_mod_four_theorem() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    assert!(
        admits_mod_four_refutation(&mut d, 3, "no_three"),
        "3 = 3 (mod 4) must refute"
    );
    assert!(
        admits_mod_four_refutation(&mut d, 7, "no_seven"),
        "7 = 3 (mod 4) must refute"
    );
    assert!(
        admits_mod_four_refutation(&mut d, 11, "no_eleven"),
        "11 = 3 (mod 4) must refute"
    );
}

/// The negative half: the same route must FAIL at the residues that are not
/// `3`, and in particular at the three primes the positive battery witnesses.
///
/// Without this the refutation battery would pass for a theorem whose
/// hypothesis was vacuous or whose modulus was wrong — `5 % 4 = 1`,
/// `13 % 4 = 1`, `17 % 4 = 1`, so `Eq.refl 3` cannot check against any of
/// them, and `4 % 4 = 0` covers the even residue as well.
#[test]
fn the_mod_four_refutation_does_not_apply_off_the_residue() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    for (n, label) in [
        (4_u32, "off_four"),
        (5, "off_five"),
        (13, "off_thirteen"),
        (17, "off_seventeen"),
    ] {
        assert!(
            !admits_mod_four_refutation(&mut d, n, label),
            "{n} is not 3 (mod 4) and the refutation must not apply to it"
        );
    }
}

/// `Int.sq_modEq_four_zero_or_one` at a concrete odd argument really lands in
/// the `1` disjunct: `3² = 9 ≡ 1 (mod 4)`.
///
/// The theorem is a disjunction, so admitting it says nothing about WHICH side
/// holds at a given argument. This settles that by reduction instead: `9 % 4`
/// and `1 % 4` agree, and `9 % 4` and `0 % 4` do not.
#[test]
fn nine_is_one_mod_four_and_not_zero() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let three = int_num(&mut d, 3);
    let four = int_num(&mut d, 4);
    let nine = d.imul(three, three);
    let residue = d.iemod(nine, four);

    let one = d.ione();
    let one_res = d.iemod(one, four);
    assert!(
        d.kernel().def_eq(residue, one_res),
        "3*3 must reduce to 1 modulo 4"
    );
    let zero = d.izero();
    let zero_res = d.iemod(zero, four);
    assert!(
        !d.kernel().def_eq(residue, zero_res),
        "3*3 must NOT reduce to 0 modulo 4"
    );

    // And the even side, so the disjunction is exercised in both directions:
    // `2² = 4 ≡ 0 (mod 4)`.
    let two = int_num(&mut d, 2);
    let foursq = d.imul(two, two);
    let even_res = d.iemod(foursq, four);
    assert!(
        d.kernel().def_eq(even_res, zero_res),
        "2*2 must reduce to 0 modulo 4"
    );
    assert!(
        !d.kernel().def_eq(even_res, one_res),
        "2*2 must NOT reduce to 1 modulo 4"
    );
}

/// The two Brahmagupta–Fibonacci groupings state exactly the terms claimed —
/// checked at FREE VARIABLES, where nothing reduces.
///
/// This exists because the concrete battery above cannot see an operand swap.
/// `(ac−bd)²` and `(bd−ac)²` are equal at every argument, so a mutation that
/// transposes the subtraction is still a TRUE theorem and still passes a test
/// run at numerals. Only a symbolic comparison of the statement separates
/// them, and only that separates the two conjugate groupings from each other —
/// which matters, because the descent depends on getting the `'` one.
#[test]
fn the_two_identities_state_the_intended_groupings() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    // `(a²+b²)(c²+d²)`, shared by both statements.
    let norms = |d: &mut IntDev<'_>, v: &[ExprId]| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let left = d.iadd(aa, bb);
        let cc = d.imul(c, c);
        let ee = d.imul(e, e);
        let right = d.iadd(cc, ee);
        d.imul(left, right)
    };
    let square_sum = |d: &mut IntDev<'_>, u: ExprId, w: ExprId| {
        let uu = d.imul(u, u);
        let ww = d.imul(w, w);
        d.iadd(uu, ww)
    };

    // The unprimed form: `(ac−bd)² + (ad+bc)²`, and its operand-swapped twin.
    let shape_name = probe_name(&mut d, "bf_shape");
    let intended = d.int_theorem(shape_name, 4, &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let lhs = norms(d, v);
        let ac = d.imul(a, c);
        let bd = d.imul(b, e);
        let u = d.isub(ac, bd);
        let ad = d.imul(a, e);
        let bc = d.imul(b, c);
        let w = d.iadd(ad, bc);
        let rhs = square_sum(d, u, w);
        let ty = d.ieq(lhs, rhs);
        let proof = d.const_app(p.brahmagupta_fibonacci, &[a, b, c, e]);
        (ty, proof)
    });
    assert!(
        intended.is_ok(),
        "Int.brahmaguptaFibonacci must state (ac-bd)^2 + (ad+bc)^2"
    );

    let swapped_name = probe_name(&mut d, "bf_shape_swapped");
    let swapped = d.int_theorem(swapped_name, 4, &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let lhs = norms(d, v);
        let ac = d.imul(a, c);
        let bd = d.imul(b, e);
        // `bd − ac` rather than `ac − bd`: a DIFFERENT term, an EQUALLY TRUE
        // statement, and the one a concrete test cannot tell apart.
        let u = d.isub(bd, ac);
        let ad = d.imul(a, e);
        let bc = d.imul(b, c);
        let w = d.iadd(ad, bc);
        let rhs = square_sum(d, u, w);
        let ty = d.ieq(lhs, rhs);
        let proof = d.const_app(p.brahmagupta_fibonacci, &[a, b, c, e]);
        (ty, proof)
    });
    assert!(
        swapped.is_err(),
        "the operand-swapped subtraction is a different statement and must not check"
    );

    // The primed form: `(ac+bd)² + (ad−bc)²`, and the unprimed grouping as its
    // control — this is the pair the descent actually has to keep straight.
    let primed_name = probe_name(&mut d, "bf_prime_shape");
    let primed = d.int_theorem(primed_name, 4, &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let lhs = norms(d, v);
        let ac = d.imul(a, c);
        let bd = d.imul(b, e);
        let u = d.iadd(ac, bd);
        let ad = d.imul(a, e);
        let bc = d.imul(b, c);
        let w = d.isub(ad, bc);
        let rhs = square_sum(d, u, w);
        let ty = d.ieq(lhs, rhs);
        let proof = d.const_app(p.brahmagupta_fibonacci_swap, &[a, b, c, e]);
        (ty, proof)
    });
    assert!(
        primed.is_ok(),
        "Int.brahmaguptaFibonacci' must state (ac+bd)^2 + (ad-bc)^2"
    );

    let crossed_name = probe_name(&mut d, "bf_prime_crossed");
    let crossed = d.int_theorem(crossed_name, 4, &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let lhs = norms(d, v);
        let ac = d.imul(a, c);
        let bd = d.imul(b, e);
        let u = d.isub(ac, bd);
        let ad = d.imul(a, e);
        let bc = d.imul(b, c);
        let w = d.iadd(ad, bc);
        let rhs = square_sum(d, u, w);
        let ty = d.ieq(lhs, rhs);
        // The UNPRIMED grouping's proof against the PRIMED statement.
        let proof = d.const_app(p.brahmagupta_fibonacci_swap, &[a, b, c, e]);
        (ty, proof)
    });
    assert!(
        crossed.is_err(),
        "the two groupings are different statements and must not be interchangeable"
    );
}

/// Try to admit `Int.descentStep` at a fully concrete instance.
///
/// Returns the verdict so the caller can require both outcomes. Every
/// hypothesis is supplied as `Eq.refl`, so the kernel has to compute both
/// sides of each of the five equations itself — a wrong quotient makes one of
/// them fail to check and the whole application is refused.
#[allow(clippy::too_many_arguments)]
fn admits_descent_instance(
    d: &mut IntDev<'_>,
    m: u32,
    pp: u32,
    q: u32,
    a: u32,
    b: u32,
    c: u32,
    e: u32,
    u: u32,
    w: u32,
    label: &str,
) -> bool {
    let prelude = d.int();
    let mi = int_num(d, m);
    let pi = int_num(d, pp);
    let qi = int_num(d, q);
    let ai = int_num(d, a);
    let bi = int_num(d, b);
    let ci = int_num(d, c);
    let ei = int_num(d, e);
    let ui = int_num(d, u);
    let wi = int_num(d, w);

    let hm = ofnat_ne(d, m, 0);
    let h1 = {
        let lhs = d.imul(mi, pi);
        d.irefl(lhs)
    };
    let h2 = {
        let lhs = d.imul(mi, qi);
        d.irefl(lhs)
    };
    let h3 = {
        let lhs = d.imul(mi, ui);
        d.irefl(lhs)
    };
    let h4 = {
        let lhs = d.imul(mi, wi);
        d.irefl(lhs)
    };
    let proof = d.const_app(
        prelude.descent_step,
        &[mi, pi, qi, ai, bi, ci, ei, ui, wi, hm, h1, h2, h3, h4],
    );
    let ty = {
        let qp = d.imul(qi, pi);
        let uu = d.imul(ui, ui);
        let ww = d.imul(wi, wi);
        let sum = d.iadd(uu, ww);
        d.ieq(qp, sum)
    };
    let name = probe_name(d, label);
    d.declare_theorem(name, ty, proof).is_ok()
}

/// The worked descent instance behind Fermat's theorem at `p = 13`.
///
/// `5² + 1² = 26 = 2·13`, so the multiplier is `m = 2`. The balanced
/// representatives of `5` and `1` modulo `2` are `c = 1` and `e = 1`, giving
/// `c² + e² = 2 = 2·1`, so the NEW multiplier is `q = 1`. The quotients are
/// `u = (ac+be)/m = 6/2 = 3` and `w = (ae−bc)/m = 4/2 = 2`, and the
/// conclusion `1·13 = 3² + 2²` is the representation `13 = 9 + 4`.
///
/// The largest magnitude formed is `26`, well inside this kernel's unary
/// numerals.
#[test]
fn the_descent_step_carries_the_worked_instance_of_thirteen() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    assert!(
        admits_descent_instance(&mut d, 2, 13, 1, 5, 1, 1, 1, 3, 2, "descent_thirteen"),
        "the m=2 descent from 2*13 = 5^2+1^2 down to 1*13 = 3^2+2^2 must check"
    );
}

/// The negative half: a WRONG quotient is refused.
///
/// `u = 2` makes the third hypothesis `2·2 = 5·1 + 1·1` read `4 = 6`, and
/// `w = 3` makes the fourth read `6 = 4`. Without these the positive test
/// above would pass for a `descentStep` whose hypotheses were vacuous or whose
/// conclusion did not depend on `u` and `w`.
#[test]
fn a_wrong_quotient_is_refused_by_the_descent_step() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    assert!(
        !admits_descent_instance(&mut d, 2, 13, 1, 5, 1, 1, 1, 2, 2, "descent_bad_u"),
        "u = 2 does not satisfy 2*u = 5*1 + 1*1 and must be refused"
    );
    assert!(
        !admits_descent_instance(&mut d, 2, 13, 1, 5, 1, 1, 1, 3, 3, "descent_bad_w"),
        "w = 3 does not satisfy 2*w = 5*1 - 1*1 and must be refused"
    );
}

/// The conclusion's multiplier is the NEW one (`q`), not the old one (`m`) —
/// which is the entire content of calling this a *descent*.
///
/// At the worked instance `q = 1` and `m = 2`, so `q·p = 13` while
/// `m·p = 26`; the theorem's own instance checks against the first and must
/// not check against the second. A `descentStep` whose conclusion kept `m`
/// would be a true statement about products and useless for induction, and
/// nothing else in this file would notice.
#[test]
fn the_descent_step_concludes_at_the_new_multiplier() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let two = int_num(&mut d, 2);
    let thirteen = int_num(&mut d, 13);
    let one = int_num(&mut d, 1);
    let five = int_num(&mut d, 5);
    let three = int_num(&mut d, 3);

    let hm = ofnat_ne(&mut d, 2, 0);
    let h1 = {
        let lhs = d.imul(two, thirteen);
        d.irefl(lhs)
    };
    let h2 = {
        let lhs = d.imul(two, one);
        d.irefl(lhs)
    };
    let h3 = {
        let lhs = d.imul(two, three);
        d.irefl(lhs)
    };
    let h4 = {
        let lhs = d.imul(two, two);
        d.irefl(lhs)
    };
    let proof = d.const_app(
        p.descent_step,
        &[
            two, thirteen, one, five, one, one, one, three, two, hm, h1, h2, h3, h4,
        ],
    );
    let squares = {
        let uu = d.imul(three, three);
        let ww = d.imul(two, two);
        d.iadd(uu, ww)
    };

    let new_multiplier = {
        let qp = d.imul(one, thirteen);
        d.ieq(qp, squares)
    };
    let name = probe_name(&mut d, "descent_new_multiplier");
    assert!(
        d.declare_theorem(name, new_multiplier, proof).is_ok(),
        "the conclusion must be q*p = u^2 + w^2, i.e. 1*13 = 9 + 4"
    );

    let old_multiplier = {
        let mp = d.imul(two, thirteen);
        d.ieq(mp, squares)
    };
    let name = probe_name(&mut d, "descent_old_multiplier");
    assert!(
        d.declare_theorem(name, old_multiplier, proof).is_err(),
        "the conclusion must NOT be m*p = u^2 + w^2 — 2*13 = 26, not 13"
    );
}

/// `Int.modEq_descent_cross_terms` at the same worked instance: with `m = 2`,
/// `a = 5`, `b = 1` and the balanced representatives `c = e = 1`, BOTH cross
/// terms `ac+be = 6` and `ae−bc = 4` are divisible by `2`.
///
/// The theorem is applied for real — every hypothesis is `Eq.refl` over a
/// congruence the kernel computes — and the reduction is checked separately in
/// both directions, including at a `c` that is NOT congruent to `a`, where the
/// first cross term becomes odd.
#[test]
fn the_cross_terms_are_divisible_by_the_multiplier() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let two = int_num(&mut d, 2);
    let five = int_num(&mut d, 5);
    let one = int_num(&mut d, 1);
    let zero = d.izero();

    // The theorem, applied.
    let hpos = {
        let j = d.num(1);
        pos_of_nat_succ(&mut d, j)
    };
    // Each `Eq.refl` has to be taken at the COMMON REDUCT of the congruence's
    // two sides, not at either side: `ModEq 2 1 5` unfolds to
    // `Eq Int (emod 1 2) (emod 5 2)`, both of which reduce to `1`, so the
    // witness is `Eq.refl 1`. Taking it at `5` — or, for `h0` below, at
    // `5*5 + 1*1` — does not check, which is how the first draft of this test
    // failed.
    let hc = d.irefl(one);
    let he = d.irefl(one);
    let h0 = d.irefl(zero);
    let applied = d.const_app(
        p.mod_eq_descent_cross_terms,
        &[two, five, one, one, one, hpos, hc, he, h0],
    );
    let ty = {
        let ac = d.imul(five, one);
        let be = d.imul(one, one);
        let first = d.iadd(ac, be);
        let ae = d.imul(five, one);
        let bc = d.imul(one, one);
        let second = d.isub(ae, bc);
        let left = imodeq(&mut d, two, first, zero);
        let right = imodeq(&mut d, two, second, zero);
        d.and(left, right)
    };
    let name = probe_name(&mut d, "cross_terms_two_five_one");
    assert!(
        d.declare_theorem(name, ty, applied).is_ok(),
        "the cross terms at (m,a,b,c,e) = (2,5,1,1,1) must both be 0 mod 2"
    );

    // And the arithmetic, by reduction, in both directions.
    let zero_res = d.iemod(zero, two);
    let good = {
        let ac = d.imul(five, one);
        let be = d.imul(one, one);
        let sum = d.iadd(ac, be);
        d.iemod(sum, two)
    };
    assert!(
        d.kernel().def_eq(good, zero_res),
        "5*1 + 1*1 = 6 must be 0 mod 2"
    );
    // `c = 0` is NOT congruent to `a = 5` mod 2, and the first cross term
    // becomes `5*0 + 1*1 = 1`, which is odd.
    let bad = {
        let ac = d.imul(five, zero);
        let be = d.imul(one, one);
        let sum = d.iadd(ac, be);
        d.iemod(sum, two)
    };
    assert!(
        !d.kernel().def_eq(bad, zero_res),
        "5*0 + 1*1 = 1 must NOT be 0 mod 2 — otherwise the congruence \
         hypotheses are doing no work"
    );
}

/// `Int.modEq_descent_cross_terms` states its two conjuncts in the order
/// claimed — checked at FREE VARIABLES, because at the worked instance it
/// cannot be checked at all.
///
/// **Measured 2026-09-05.** A mutant that transposed both the conjunction and
/// its `And.intro` survived every other test in this file, 0 kills of 15. The
/// reason is exact: at `(m,a,b,c,e) = (2,5,1,1,1)` the two conjuncts are
/// `ModEq 2 6 0` and `ModEq 2 4 0`, both of which unfold to
/// `Eq Int (emod _ 2) (emod 0 2)` and REDUCE to the same closed proposition
/// `Eq Int 0 0` — so `And left right` and `And right left` are definitionally
/// equal there and the concrete battery cannot separate them. This test is the
/// repair, and it kills that mutant.
#[test]
fn the_cross_term_conjuncts_are_ordered_as_stated() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    // `∀ m a b c e, 0 < m → ModEq m c a → ModEq m e b →
    //   ModEq m (a*a + b*b) 0 → <conjunction>`, proved by the theorem itself.
    let build = |d: &mut IntDev<'_>, v: &[ExprId], swap: bool| {
        let (m, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, m);
        let hc_ty = imodeq(d, m, c, a);
        let he_ty = imodeq(d, m, e, b);
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let norm = d.iadd(aa, bb);
        let h0_ty = imodeq(d, m, norm, zero);

        let ac = d.imul(a, c);
        let be = d.imul(b, e);
        let first = d.iadd(ac, be);
        let ae = d.imul(a, e);
        let bc = d.imul(b, c);
        let second = d.isub(ae, bc);
        let left = imodeq(d, m, first, zero);
        let right = imodeq(d, m, second, zero);
        let concl = if swap {
            d.and(right, left)
        } else {
            d.and(left, right)
        };

        let ty = {
            let s3 = d.arrow(h0_ty, concl);
            let s2 = d.arrow(he_ty, s3);
            let s1 = d.arrow(hc_ty, s2);
            d.arrow(pos_ty, s1)
        };

        let pos_fv = d.fresh_fvar();
        let hpos = d.kernel().fvar(pos_fv);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let he_fv = d.fresh_fvar();
        let he = d.kernel().fvar(he_fv);
        let h0_fv = d.fresh_fvar();
        let h0 = d.kernel().fvar(h0_fv);
        let applied = d.const_app(
            p.mod_eq_descent_cross_terms,
            &[m, a, b, c, e, hpos, hc, he, h0],
        );
        let l3 = d.lam_fv(h0_fv, h0_ty, applied);
        let l2 = d.lam_fv(he_fv, he_ty, l3);
        let l1 = d.lam_fv(hc_fv, hc_ty, l2);
        let proof = d.lam_fv(pos_fv, pos_ty, l1);
        (ty, proof)
    };

    let stated_name = probe_name(&mut d, "cross_terms_shape");
    let stated = d.int_theorem(stated_name, 5, &|d, v| build(d, v, false));
    assert!(
        stated.is_ok(),
        "the first conjunct must be about a*c + b*e and the second about a*e - b*c"
    );

    let swapped_name = probe_name(&mut d, "cross_terms_shape_swapped");
    let swapped = d.int_theorem(swapped_name, 5, &|d, v| build(d, v, true));
    assert!(
        swapped.is_err(),
        "the transposed conjunction is a different statement and must not check"
    );
}

/// Every declaration this module adds is present AND has an empty axiom
/// footprint.
///
/// The `contains` check comes FIRST and is not decoration: `axiom_footprint`
/// returns an empty set for a name that does not exist, so a misspelled or
/// never-declared name would otherwise pass the footprint assertion silently
/// (`CLAUDE.md`, "an empty footprint is also what a missing name returns").
#[test]
fn every_two_squares_declaration_is_present_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let names = [
        ("Int.IsSumOfTwoSquares", p.is_sum_of_two_squares),
        ("Int.isSumOfTwoSquares_intro", p.is_sum_of_two_squares_intro),
        ("Int.brahmaguptaFibonacci", p.brahmagupta_fibonacci),
        ("Int.brahmaguptaFibonacci'", p.brahmagupta_fibonacci_swap),
        ("Int.isSumOfTwoSquares_mul", p.is_sum_of_two_squares_mul),
        ("Int.sq_of_two_mul", p.sq_of_two_mul),
        ("Int.sq_of_two_mul_add_one", p.sq_of_two_mul_add_one),
        (
            "Int.sq_modEq_four_zero_or_one",
            p.sq_mod_eq_four_zero_or_one,
        ),
        (
            "Int.not_isSumOfTwoSquares_of_modEq_four_three",
            p.not_is_sum_of_two_squares_of_mod_eq_four_three,
        ),
        ("Int.zero_add", p.zero_add),
        ("Int.sub_self", p.sub_self),
        ("Int.add_sub_cancel_right", p.add_sub_cancel_right),
        ("Int.mul_sub_mul_comm", p.mul_sub_mul_comm),
        ("Int.eq_of_sub_eq_zero", p.eq_of_sub_eq_zero),
        ("Int.mul_ne_zero", p.mul_ne_zero),
        (
            "Int.mul_left_cancel_of_ne_zero",
            p.mul_left_cancel_of_ne_zero,
        ),
        (
            "Int.modEq_descent_cross_terms",
            p.mod_eq_descent_cross_terms,
        ),
        ("Int.mul_mul_of_mul_mul", p.mul_mul_of_mul_mul),
        ("Int.sq_add_sq_of_mul_left", p.sq_add_sq_of_mul_left),
        ("Int.descentStep", p.descent_step),
    ];
    for (label, name) in names {
        assert!(
            k.environment().contains(name),
            "{label} must be declared before its footprint means anything"
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free, found {} axioms",
            footprint.len()
        );
    }
}
