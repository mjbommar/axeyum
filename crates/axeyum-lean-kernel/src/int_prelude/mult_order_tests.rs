//! Evaluation tests and negative controls for `mult_order.rs`.
//!
//! `Int.IsOrder` and `Int.IsPrimitiveRoot` are `Definition`s, and the trusted
//! gate cannot tell you a `Definition` is wrong — it type-checks either way
//! (`CLAUDE.md`, "the declaration is rejected, or admitted and wrong"). So
//! every claim here is settled by **reduction at concrete small arguments**,
//! with the assertion's outcome depending on the finding in both directions:
//! each battery asserts what must hold AND what must fail.
//!
//! The magnitudes are deliberately tiny. `Nat` numerals are unary and cost is
//! superlinear in the largest magnitude formed, so the worked cases are
//! `ord_8(3) = 2` (largest term `3^4 = 81`) and `ord_3(2) = 2` (largest term
//! `2^2 = 4`). The one expensive case, `ord_7(3) = 6`, forms `3^6 = 729` and
//! is confined to a single `def_eq` battery
//! ([`multiplicative_order_of_three_mod_seven_is_six_by_reduction`]) that
//! builds no proof terms.

use super::super::{Kernel, build_int_prelude};
use super::ops::IntDev;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `emod (pow a m) n` and `emod one n` agree by pure reduction — i.e. the
/// kernel itself computes `a^m ≡ 1 (mod n)`.
///
/// Returns the verdict rather than asserting, so a caller can require BOTH
/// outcomes and no run can be vacuous.
fn kills_by_reduction(d: &mut IntDev<'_>, n: u32, a: u32, m: u32) -> bool {
    let n_i = {
        let nn = d.num(n);
        d.of_nat(nn)
    };
    let a_i = {
        let aa = d.num(a);
        d.of_nat(aa)
    };
    let m_n = d.num(m);
    let pow_am = d.ipow(a_i, m_n);
    let one_i = d.ione();
    let lhs = d.iemod(pow_am, n_i);
    let rhs = d.iemod(one_i, n_i);
    d.kernel().def_eq(lhs, rhs)
}

/// `Le a b` at concrete numerals, via `Nat.le_intro a b (b-a) rfl`.
fn concrete_le(d: &mut IntDev<'_>, a: u32, b: u32) -> ExprId {
    assert!(a <= b, "concrete_le is only for a <= b");
    let av = d.num(a);
    let bv = d.num(b);
    let kv = d.num(b - a);
    let refl = d.refl(bv);
    let f = d.int().nat.le_intro;
    d.const_app(f, &[av, bv, kv, refl])
}

/// `Not (Eq Int (ofNat x) (ofNat y))` for distinct small `x`, `y`, by pushing
/// the equation through `Int.natAbs` onto `Nat` and refuting it with
/// `Nat.ne_of_beq_eq_false`.
fn ofnat_ne(d: &mut IntDev<'_>, x: u32, y: u32) -> ExprId {
    assert!(x != y, "ofnat_ne is only for distinct numerals");
    let p = d.int();
    let xv = d.num(x);
    let yv = d.num(y);
    let xi = d.of_nat(xv);
    let yi = d.of_nat(yv);

    let h_ty = d.ieq(xi, yi);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // `Eq Nat x (natAbs (ofNat x))` is `Eq Nat x x`; transport along `h`.
    let start = d.refl(xv);
    let moved = d.int_eq_rewrite(xi, yi, h, start, &|d, z| {
        let na = d.const_app(p.nat_abs, &[z]);
        d.eq(xv, na)
    });
    // `Nat.beq x y = false` by reduction.
    let false_b = d.bool_false();
    let hbeq = d.bool_refl(false_b);
    let body = {
        let f = d.int().nat.ne_of_beq_eq_false;
        d.const_app(f, &[xv, yv, hbeq, moved])
    };
    d.lam_fv(h_fv, h_ty, body)
}

/// `Int.IsOrder` unfolds to exactly the conjunction the module doc claims —
/// and NOT to the transposed variant with the positivity comparison the wrong
/// way round.
///
/// A `Definition` with `Lt k zero` in place of `Lt zero k` type-checks
/// identically and is admitted identically; only this comparison sees it.
#[test]
fn is_order_unfolds_to_the_intended_conjunction() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let kk_fv = d.fresh_fvar();
    let kk = d.kernel().fvar(kk_fv);
    let _ = (int_ty, nat);

    let stated = d.const_app(p.is_order, &[n, a, kk]);

    let zero_nat = NatOps::zero(&mut d);
    let one_i = d.ione();
    let expected = {
        let pos = d.lt(zero_nat, kk);
        let pow_ak = d.ipow(a, kk);
        let hit = d.const_app(p.mod_eq, &[n, pow_ak, one_i]);
        let least = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let pow_aj = d.ipow(a, j);
            let hj = d.const_app(p.mod_eq, &[n, pow_aj, one_i]);
            let nhj = d.not(hj);
            let jlt = d.lt(j, kk);
            let inner = d.arrow(jlt, nhj);
            let jpos = d.lt(zero_nat, j);
            let with_pos = d.arrow(jpos, inner);
            let nat_ty = d.nat_ty();
            d.pi_fv(j_fv, nat_ty, with_pos)
        };
        let tail = d.and(hit, least);
        d.and(pos, tail)
    };
    assert!(
        d.kernel().def_eq(stated, expected),
        "Int.IsOrder must unfold to `0 < k ∧ (a^k ≡ 1 ∧ minimality)`"
    );

    // The transposed positivity conjunct is a DIFFERENT proposition; if this
    // were def_eq the check above would prove nothing.
    let transposed = {
        let pos = d.lt(kk, zero_nat);
        let pow_ak = d.ipow(a, kk);
        let hit = d.const_app(p.mod_eq, &[n, pow_ak, one_i]);
        let least = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let pow_aj = d.ipow(a, j);
            let hj = d.const_app(p.mod_eq, &[n, pow_aj, one_i]);
            let nhj = d.not(hj);
            let jlt = d.lt(j, kk);
            let inner = d.arrow(jlt, nhj);
            let jpos = d.lt(zero_nat, j);
            let with_pos = d.arrow(jpos, inner);
            let nat_ty = d.nat_ty();
            d.pi_fv(j_fv, nat_ty, with_pos)
        };
        let tail = d.and(hit, least);
        d.and(pos, tail)
    };
    assert!(
        !d.kernel().def_eq(stated, transposed),
        "the transposed positivity conjunct must NOT be definitionally the \
         same proposition -- otherwise the assertion above is vacuous"
    );
}

/// The exponents that kill `3` modulo `8` are exactly the multiples of `2`.
///
/// This is simultaneously the evaluation test for `Int.pow`/`Int.ModEq` at
/// concrete arguments and the negative control for
/// `Int.pow_modeq_one_of_dvd`: `2 ∤ 1` and `2 ∤ 3`, and at those exponents the
/// conclusion genuinely FAILS. A theorem that dropped its divisibility
/// hypothesis would be refuted here.
#[test]
fn three_mod_eight_is_killed_by_exactly_the_even_exponents() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    for m in [0u32, 2, 4] {
        assert!(
            kills_by_reduction(&mut d, 8, 3, m),
            "3^{m} must be congruent to 1 mod 8"
        );
    }
    for m in [1u32, 3, 5] {
        assert!(
            !kills_by_reduction(&mut d, 8, 3, m),
            "3^{m} must NOT be congruent to 1 mod 8"
        );
    }
}

/// `ord_7(3) = 6` — the second discriminating case, by reduction only.
///
/// Kept to `def_eq` rather than a proof term because it forms `3^6 = 729`, and
/// every `Nat` numeral in this kernel is unary.
#[test]
fn multiplicative_order_of_three_mod_seven_is_six_by_reduction() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    for m in 1u32..=5 {
        assert!(
            !kills_by_reduction(&mut d, 7, 3, m),
            "3^{m} must NOT be congruent to 1 mod 7 -- the order is 6"
        );
    }
    assert!(
        kills_by_reduction(&mut d, 7, 3, 6),
        "3^6 must be congruent to 1 mod 7"
    );
}

/// A full kernel-checked `Int.IsOrder (ofNat 8) (ofNat 3) 2`, plus the
/// non-vacuity control that `Int.IsOrder (ofNat 8) (ofNat 3) 4` is REFUTABLE.
///
/// `φ(8) = 4`, so `4` is a perfectly good killing exponent and only the
/// minimality conjunct separates it from the order. A definition that lost
/// minimality would admit both halves; this test admits one and refutes the
/// other, so it cannot pass under that mutation.
#[test]
fn three_has_multiplicative_order_two_mod_eight() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let eight = d.num(8);
    let three = d.num(3);
    let two = d.num(2);
    let one_nat = d.num(1);
    let four = d.num(4);
    let n8 = d.of_nat(eight);
    let a3 = d.of_nat(three);

    // -- the positive half: IsOrder (ofNat 8) (ofNat 3) 2 --------------------
    let pos = concrete_le(&mut d, 1, 2); // Lt 0 2 is Le 1 2
    let one_i = d.ione();
    let pow_a2 = d.ipow(a3, two);
    let hit_ty = d.const_app(p.mod_eq, &[n8, pow_a2, one_i]);
    let hit = {
        let lhs = d.iemod(pow_a2, n8);
        d.irefl(lhs)
    };

    let least_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pow_aj = d.ipow(a3, j);
        let hj = d.const_app(p.mod_eq, &[n8, pow_aj, one_i]);
        let nhj = d.not(hj);
        let jlt = d.lt(j, two);
        let inner = d.arrow(jlt, nhj);
        let zero_nat = NatOps::zero(&mut d);
        let jpos = d.lt(zero_nat, j);
        let with_pos = d.arrow(jpos, inner);
        let nat_ty = d.nat_ty();
        d.pi_fv(j_fv, nat_ty, with_pos)
    };
    let least = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let zero_nat = NatOps::zero(&mut d);
        let jpos_ty = d.lt(zero_nat, j);
        let jpos_fv = d.fresh_fvar();
        let jpos = d.kernel().fvar(jpos_fv);
        let jlt_ty = d.lt(j, two);
        let jlt_fv = d.fresh_fvar();
        let jlt = d.kernel().fvar(jlt_fv);

        // `0 < j` and `j < 2` pin `j = 1`.
        let le_j_one = {
            // `j < 2` is `Le (succ j) (succ 1)`; cancel the successors.
            let f = d.int().nat.le_of_succ_le_succ;
            d.const_app(f, &[j, one_nat, jlt])
        };
        let j_eq_one = {
            let f = d.int().nat.le_antisymm;
            d.const_app(f, &[j, one_nat, le_j_one, jpos])
        };
        // `3^1 mod 8 = 3 ≠ 1 = 1 mod 8`.
        let not_at_one = ofnat_ne(&mut d, 3, 1);
        let moved = {
            let back = d.symm(j, one_nat, j_eq_one);
            d.nat_rewrite(one_nat, j, back, not_at_one, &|d, x| {
                let pow_ax = d.ipow(a3, x);
                let hx = d.const_app(p.mod_eq, &[n8, pow_ax, one_i]);
                d.not(hx)
            })
        };
        let b0 = d.lam_fv(jlt_fv, jlt_ty, moved);
        let b1 = d.lam_fv(jpos_fv, jpos_ty, b0);
        let nat_ty = d.nat_ty();
        d.lam_fv(j_fv, nat_ty, b1)
    };

    let tail_ty = d.and(hit_ty, least_ty);
    let tail = {
        let f = d.int().logic.and_intro;
        d.const_app(f, &[hit_ty, least_ty, hit, least])
    };
    let pos_ty = {
        let zero_nat = NatOps::zero(&mut d);
        d.lt(zero_nat, two)
    };
    let witness = {
        let f = d.int().logic.and_intro;
        d.const_app(f, &[pos_ty, tail_ty, pos, tail])
    };
    let stated = d.const_app(p.is_order, &[n8, a3, two]);
    let inferred = d
        .kernel()
        .infer(witness)
        .unwrap_or_else(|e| panic!("the ord_8(3) = 2 witness must type-check: {e:?}"));
    assert!(
        d.kernel().def_eq(inferred, stated),
        "the witness must land on Int.IsOrder (ofNat 8) (ofNat 3) 2"
    );

    // -- the control: IsOrder (ofNat 8) (ofNat 3) 4 is REFUTABLE -------------
    // From its own minimality clause at `j = 2`, against the `3^2 ≡ 1` above.
    let ord4_ty = d.const_app(p.is_order, &[n8, a3, four]);
    let ord4_fv = d.fresh_fvar();
    let ord4 = d.kernel().fvar(ord4_fv);
    let refutation = {
        let least4_ty = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let pow_aj = d.ipow(a3, j);
            let hj = d.const_app(p.mod_eq, &[n8, pow_aj, one_i]);
            let nhj = d.not(hj);
            let jlt = d.lt(j, four);
            let inner = d.arrow(jlt, nhj);
            let zero_nat = NatOps::zero(&mut d);
            let jpos = d.lt(zero_nat, j);
            let with_pos = d.arrow(jpos, inner);
            let nat_ty = d.nat_ty();
            d.pi_fv(j_fv, nat_ty, with_pos)
        };
        let hit4_ty = {
            let pow_a4 = d.ipow(a3, four);
            d.const_app(p.mod_eq, &[n8, pow_a4, one_i])
        };
        let pos4_ty = {
            let zero_nat = NatOps::zero(&mut d);
            d.lt(zero_nat, four)
        };
        let tail4_ty = d.and(hit4_ty, least4_ty);
        let rest = d.and_right(pos4_ty, tail4_ty, ord4);
        let least4 = d.and_right(hit4_ty, least4_ty, rest);
        let two_pos = concrete_le(&mut d, 1, 2);
        let two_lt_four = concrete_le(&mut d, 3, 4);
        let refuted = d.apply(least4, &[two, two_pos, two_lt_four]);
        d.apply(refuted, &[hit])
    };
    let refutation_fn = d.lam_fv(ord4_fv, ord4_ty, refutation);
    let refutation_ty = d.kernel().infer(refutation_fn).unwrap_or_else(|e| {
        panic!("the refutation of IsOrder (ofNat 8) (ofNat 3) 4 must type-check: {e:?}")
    });
    let expected_not = d.not(ord4_ty);
    assert!(
        d.kernel().def_eq(refutation_ty, expected_not),
        "4 is a killing exponent for 3 mod 8 but NOT the order -- only the \
         minimality conjunct separates them, and this refutation is what \
         proves the definition carries it"
    );
}

/// `2` is a primitive root mod `3`, and `3` is NOT one mod `8`.
///
/// The negative case is the discriminating one: `φ(8) = 4` while `ord_8(3) =
/// 2`, so a `IsPrimitiveRoot` that forgot minimality — or that compared the
/// order against the wrong quantity — would admit it.
#[test]
fn primitive_roots_at_concrete_moduli() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let one_i = d.ione();
    let one_nat = d.num(1);

    // -- IsPrimitiveRoot 3 2 : the order of 2 mod 3 is φ(3) = 2 --------------
    let three = d.num(3);
    let two = d.num(2);
    let n3 = d.of_nat(three);
    let a2 = d.of_nat(two);
    let t3 = d.const_app(p.nat.totient, &[three]);

    let pos = concrete_le(&mut d, 1, 2);
    let pow_a_t = d.ipow(a2, t3);
    let hit_ty = d.const_app(p.mod_eq, &[n3, pow_a_t, one_i]);
    let hit = {
        let lhs = d.iemod(pow_a_t, n3);
        d.irefl(lhs)
    };
    let least_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pow_aj = d.ipow(a2, j);
        let hj = d.const_app(p.mod_eq, &[n3, pow_aj, one_i]);
        let nhj = d.not(hj);
        let jlt = d.lt(j, t3);
        let inner = d.arrow(jlt, nhj);
        let zero_nat = NatOps::zero(&mut d);
        let jpos = d.lt(zero_nat, j);
        let with_pos = d.arrow(jpos, inner);
        let nat_ty = d.nat_ty();
        d.pi_fv(j_fv, nat_ty, with_pos)
    };
    let least = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let zero_nat = NatOps::zero(&mut d);
        let jpos_ty = d.lt(zero_nat, j);
        let jpos_fv = d.fresh_fvar();
        let jpos = d.kernel().fvar(jpos_fv);
        let jlt_ty = d.lt(j, t3);
        let jlt_fv = d.fresh_fvar();
        let jlt = d.kernel().fvar(jlt_fv);
        // `totient 3` reduces to `2`, so `j < totient 3` is `succ j ≤ 2`.
        let le_j_one = {
            // `j < 2` is `Le (succ j) (succ 1)`; cancel the successors.
            let f = d.int().nat.le_of_succ_le_succ;
            d.const_app(f, &[j, one_nat, jlt])
        };
        let j_eq_one = {
            let f = d.int().nat.le_antisymm;
            d.const_app(f, &[j, one_nat, le_j_one, jpos])
        };
        let not_at_one = ofnat_ne(&mut d, 2, 1);
        let moved = {
            let back = d.symm(j, one_nat, j_eq_one);
            d.nat_rewrite(one_nat, j, back, not_at_one, &|d, x| {
                let pow_ax = d.ipow(a2, x);
                let hx = d.const_app(p.mod_eq, &[n3, pow_ax, one_i]);
                d.not(hx)
            })
        };
        let b0 = d.lam_fv(jlt_fv, jlt_ty, moved);
        let b1 = d.lam_fv(jpos_fv, jpos_ty, b0);
        let nat_ty = d.nat_ty();
        d.lam_fv(j_fv, nat_ty, b1)
    };
    let tail_ty = d.and(hit_ty, least_ty);
    let tail = {
        let f = d.int().logic.and_intro;
        d.const_app(f, &[hit_ty, least_ty, hit, least])
    };
    let pos_ty = {
        let zero_nat = NatOps::zero(&mut d);
        d.lt(zero_nat, t3)
    };
    let witness = {
        let f = d.int().logic.and_intro;
        d.const_app(f, &[pos_ty, tail_ty, pos, tail])
    };
    let stated = d.const_app(p.is_primitive_root, &[three, a2]);
    let inferred = d
        .kernel()
        .infer(witness)
        .unwrap_or_else(|e| panic!("the primitive-root witness must type-check: {e:?}"));
    assert!(
        d.kernel().def_eq(inferred, stated),
        "2 must be a primitive root mod 3 (φ(3) = 2 and ord_3(2) = 2)"
    );

    // -- Not (IsPrimitiveRoot 8 3): φ(8) = 4 but ord_8(3) = 2 ----------------
    let eight = d.num(8);
    let n8 = d.of_nat(eight);
    let three_again = d.num(3);
    let a3 = d.of_nat(three_again);
    let t8 = d.const_app(p.nat.totient, &[eight]);
    let pr_ty = d.const_app(p.is_primitive_root, &[eight, a3]);
    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);

    let two_again = d.num(2);
    let pow_a3_2 = d.ipow(a3, two_again);
    let _hit2_ty = d.const_app(p.mod_eq, &[n8, pow_a3_2, one_i]);
    let hit2 = {
        let lhs = d.iemod(pow_a3_2, n8);
        d.irefl(lhs)
    };

    let least8_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pow_aj = d.ipow(a3, j);
        let hj = d.const_app(p.mod_eq, &[n8, pow_aj, one_i]);
        let nhj = d.not(hj);
        let jlt = d.lt(j, t8);
        let inner = d.arrow(jlt, nhj);
        let zero_nat = NatOps::zero(&mut d);
        let jpos = d.lt(zero_nat, j);
        let with_pos = d.arrow(jpos, inner);
        let nat_ty = d.nat_ty();
        d.pi_fv(j_fv, nat_ty, with_pos)
    };
    let hit8_ty = {
        let pow_a_t8 = d.ipow(a3, t8);
        d.const_app(p.mod_eq, &[n8, pow_a_t8, one_i])
    };
    let pos8_ty = {
        let zero_nat = NatOps::zero(&mut d);
        d.lt(zero_nat, t8)
    };
    let tail8_ty = d.and(hit8_ty, least8_ty);
    let rest = d.and_right(pos8_ty, tail8_ty, pr);
    let least8 = d.and_right(hit8_ty, least8_ty, rest);
    let two_pos = concrete_le(&mut d, 1, 2);
    let two_lt_four = concrete_le(&mut d, 3, 4);
    let refuted = d.apply(least8, &[two_again, two_pos, two_lt_four]);
    let contra = d.apply(refuted, &[hit2]);
    let refutation_fn = d.lam_fv(pr_fv, pr_ty, contra);
    let refutation_ty = d
        .kernel()
        .infer(refutation_fn)
        .unwrap_or_else(|e| panic!("the refutation of IsPrimitiveRoot 8 3 must type-check: {e:?}"));
    let expected_not = d.not(pr_ty);
    assert!(
        d.kernel().def_eq(refutation_ty, expected_not),
        "3 must NOT be a primitive root mod 8: φ(8) = 4 but ord_8(3) = 2"
    );
}

/// Every declaration `mult_order.rs` makes is axiom-free, read from the
/// kernel rather than from source text.
#[test]
fn mult_order_declarations_are_axiom_free() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let names = [
        p.one_pow,
        p.is_order,
        p.pow_modeq_one_of_dvd,
        p.order_dvd_of_pow_modeq_one,
        p.pow_modeq_one_iff_order_dvd,
        p.order_unique,
        p.order_exists,
        p.order_dvd_totient,
        p.is_primitive_root,
        p.order_pow_eq_of_le,
        p.primitive_root_pow_injective,
    ];
    for name in names {
        let shown = k.display_name(name).to_string();
        assert!(
            k.environment().iter().any(|(n, _)| *n == name),
            "{shown} must be in the environment"
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{shown} must rest on zero axioms, found {:?}",
            footprint
                .iter()
                .map(|n| k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}
