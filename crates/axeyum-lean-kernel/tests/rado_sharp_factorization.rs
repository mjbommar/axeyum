//! The exact subtraction-free finite-sum factorization and quotient-free
//! witness identity used in the proof of `thm:sharp` in
//! `../axeyum-rado-paper`.
//!
//! The generic algebra lives in [`build_nat_prelude`]. This file contributes
//! only the paper-shaped theorem and executable controls. No axiom is added.

#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]

use axeyum_lean_kernel::{
    Declaration, ExprId, Kernel, NameId, NatOps, NatPrelude, NatState, build_nat_prelude,
};

struct Dev {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
    root: NameId,
}

impl NatOps for Dev {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Dev {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude builds");
        let st = NatState::new(&mut k, p);
        let anon = k.anon();
        let root = k.name_str(anon, "radoSharp");
        Self { k, p, st, root }
    }

    fn name(&mut self, part: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, part)
    }
}

fn power_range(d: &mut Dev, a: ExprId, shifts: usize) -> ExprId {
    let i_fv = d.fresh_fvar();
    let mut exponent = d.k.fvar(i_fv);
    for _ in 0..shifts {
        exponent = d.succ(exponent);
    }
    let body = d.pow(a, exponent);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// Admit the exact factorization, parameterized by `n = k - 3`:
///
/// `a * (1 + (2*S₁(n) + a^(n+1))) = a + (2*S₂(n) + a^(n+2))`,
///
/// where `S₁(n) = Σ_{i<n} a^(i+1)` and
/// `S₂(n) = Σ_{i<n} a^(i+2)`. At `k = 3`, `n = 0` and both sums are empty.
fn admit_sharp_factorization(d: &mut Dev) -> NameId {
    let p = d.p;
    let name = d.name("factorization");
    d.theorem(name, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let one = d.num(1);
        let two = d.num(2);
        let shifted = power_range(d, a, 1);
        let double_shifted = power_range(d, a, 2);
        let sum1 = d.sum_range(shifted, n);
        let sum2 = d.sum_range(double_shifted, n);
        let sn = d.succ(n);
        let ssn = d.succ(sn);
        let power1 = d.pow(a, sn);
        let power2 = d.pow(a, ssn);
        let inner = {
            let twice_sum = d.mul(two, sum1);
            let tail = d.add(twice_sum, power1);
            d.add(one, tail)
        };
        let start = d.mul(a, inner);
        let twice_sum2 = d.mul(two, sum2);
        let end = {
            let tail = d.add(twice_sum2, power2);
            d.add(a, tail)
        };
        let stmt = d.eq(start, end);

        // First prove a*S₁(n) = S₂(n): distribute into the range and use
        // pointwise mul_comm + pow_succ under sumRange_congr.
        let scaled = {
            let i_fv = d.fresh_fvar();
            let i = d.k.fvar(i_fv);
            let si = d.succ(i);
            let power = d.pow(a, si);
            let body = d.mul(a, power);
            let nat = d.nat_ty();
            d.lam_fv(i_fv, nat, body)
        };
        let scaled_sum = d.sum_range(scaled, n);
        let a_sum1 = d.mul(a, sum1);
        let h_distribute = d.lemma(p.mul_sum_range, &[a, shifted, n]);
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.k.fvar(i_fv);
            let si = d.succ(i);
            let ssi = d.succ(si);
            let power = d.pow(a, si);
            let scaled_i = d.mul(a, power);
            let commuted = d.mul(power, a);
            let h_comm = d.lemma(p.mul_comm, &[a, power]);
            let shifted_power = d.pow(a, ssi);
            let h_pow = d.lemma(p.pow_succ, &[a, si]);
            let h_pow_rev = d.symm(shifted_power, commuted, h_pow);
            let (_, body) = d.chain(scaled_i, &[(commuted, h_comm), (shifted_power, h_pow_rev)]);
            let nat = d.nat_ty();
            d.lam_fv(i_fv, nat, body)
        };
        let h_pointwise = d.lemma(p.sum_range_congr, &[scaled, double_shifted, n, pointwise]);
        let (_, h_scaled_sum) = d.chain(a_sum1, &[(scaled_sum, h_distribute), (sum2, h_pointwise)]);

        // Expand the outer product and normalize its two nonconstant terms.
        let twice_sum1 = d.mul(two, sum1);
        let right_group = d.add(twice_sum1, power1);
        let a_one = d.mul(a, one);
        let a_right = d.mul(a, right_group);
        let step1 = d.add(a_one, a_right);
        let h1 = d.lemma(p.left_distrib, &[a, one, right_group]);
        let step2 = d.add(a, a_right);
        let h_mul_one = d.lemma(p.mul_one, &[a]);
        let h2 = d.congr(a_one, a, h_mul_one, &|d, t| d.add(t, a_right));

        let a_twice_sum = d.mul(a, twice_sum1);
        let a_power1 = d.mul(a, power1);
        let step3 = {
            let tail = d.add(a_twice_sum, a_power1);
            d.add(a, tail)
        };
        let h_inner_distrib = d.lemma(p.left_distrib, &[a, twice_sum1, power1]);
        let distributed_inner = d.add(a_twice_sum, a_power1);
        let h3 = d.congr(a_right, distributed_inner, h_inner_distrib, &|d, t| {
            d.add(a, t)
        });

        // a*(2*S₁) = (a*2)*S₁ = (2*a)*S₁ = 2*(a*S₁) = 2*S₂.
        let a_two = d.mul(a, two);
        let reassociated1 = d.mul(a_two, sum1);
        let h_assoc1 = d.lemma(p.mul_assoc, &[a, two, sum1]);
        let h_assoc1_rev = d.symm(reassociated1, a_twice_sum, h_assoc1);
        let two_a = d.mul(two, a);
        let reassociated2 = d.mul(two_a, sum1);
        let h_a_two_comm = d.lemma(p.mul_comm, &[a, two]);
        let h_comm_under_mul = d.congr(a_two, two_a, h_a_two_comm, &|d, t| d.mul(t, sum1));
        let two_a_sum = d.mul(two, a_sum1);
        let h_assoc2 = d.lemma(p.mul_assoc, &[two, a, sum1]);
        let h_scaled_under_two = d.congr(a_sum1, sum2, h_scaled_sum, &|d, t| d.mul(two, t));
        let (_, h_twice_sum) = d.chain(
            a_twice_sum,
            &[
                (reassociated1, h_assoc1_rev),
                (reassociated2, h_comm_under_mul),
                (two_a_sum, h_assoc2),
                (twice_sum2, h_scaled_under_two),
            ],
        );
        let step4 = {
            let tail = d.add(twice_sum2, a_power1);
            d.add(a, tail)
        };
        let h4 = d.congr(a_twice_sum, twice_sum2, h_twice_sum, &|d, t| {
            let tail = d.add(t, a_power1);
            d.add(a, tail)
        });

        // a*a^(n+1) = a^(n+1)*a = a^(n+2).
        let commuted_power = d.mul(power1, a);
        let h_power_comm = d.lemma(p.mul_comm, &[a, power1]);
        let h_power_succ = d.lemma(p.pow_succ, &[a, sn]);
        let h_power_succ_rev = d.symm(power2, commuted_power, h_power_succ);
        let (_, h_power2) = d.chain(
            a_power1,
            &[(commuted_power, h_power_comm), (power2, h_power_succ_rev)],
        );
        let h5 = d.congr(a_power1, power2, h_power2, &|d, t| {
            let tail = d.add(twice_sum2, t);
            d.add(a, tail)
        });
        let (_, proof) = d.chain(
            start,
            &[
                (step1, h1),
                (step2, h2),
                (step3, h3),
                (step4, h4),
                (end, h5),
            ],
        );
        (stmt, proof)
    })
    .expect("sharp factorization checks");
    name
}

/// Admit the quotient-free algebraic identity for the paper witness. The
/// explicit factor `N = b*q` replaces `q = N/b`, and `a <= q` is exactly the
/// side condition needed for `u = q-a` in truncated natural arithmetic.
///
/// With `X = N-a*b+1`, `Y = 1`, `u = q-a`, and `Z = a*u`, prove
/// `a*(X-Y) = b*Z`.
fn admit_sharp_witness_identity(d: &mut Dev) -> NameId {
    let p = d.p;
    let name = d.name("witness_identity");
    d.theorem(name, 4, &|d, v| {
        let (a, b, n, q) = (v[0], v[1], v[2], v[3]);
        let bq = d.mul(b, q);
        let factor_ty = d.eq(n, bq);
        let factor_fv = d.fresh_fvar();
        let factor = d.k.fvar(factor_fv);
        let bound_ty = d.le(a, q);
        let bound_fv = d.fresh_fvar();
        let bound = d.k.fvar(bound_fv);

        let u = d.sub(q, a);
        let ab = d.mul(a, b);
        let ba = d.mul(b, a);
        let n_sub_ab = d.sub(n, ab);
        let one = d.num(1);
        let x = d.add(n_sub_ab, one);
        let y = one;
        let z = d.mul(a, u);
        let x_sub_y = d.sub(x, y);
        let lhs = d.mul(a, x_sub_y);
        let rhs = d.mul(b, z);
        let conclusion = d.eq(lhs, rhs);

        // N-a*b = b*(q-a): rewrite the explicit factor and commute a*b,
        // then use the generic bounded multiplication/subtraction theorem.
        let bq_sub_ab = d.sub(bq, ab);
        let h_factor_sub = d.congr(n, bq, factor, &|d, t| d.sub(t, ab));
        let bq_sub_ba = d.sub(bq, ba);
        let h_ab_ba = d.lemma(p.mul_comm, &[a, b]);
        let h_comm_sub = d.congr(ab, ba, h_ab_ba, &|d, t| d.sub(bq, t));
        let bu = d.mul(b, u);
        let h_mul_sub = d.lemma(p.mul_sub_left_distrib, &[b, q, a, bound]);
        let h_mul_sub_rev = d.symm(bu, bq_sub_ba, h_mul_sub);
        let (_end, difference_eq_bu) = d.chain(
            n_sub_ab,
            &[
                (bq_sub_ab, h_factor_sub),
                (bq_sub_ba, h_comm_sub),
                (bu, h_mul_sub_rev),
            ],
        );

        // Scale that equality by `a`, then reassociate and commute the two
        // scalar factors to reach `b*(a*u)`.
        let a_bu = d.mul(a, bu);
        let h_scaled = d.congr(n_sub_ab, bu, difference_eq_bu, &|d, t| d.mul(a, t));
        let ab_u = d.mul(ab, u);
        let h_assoc_a = d.lemma(p.mul_assoc, &[a, b, u]);
        let h_assoc_a_rev = d.symm(ab_u, a_bu, h_assoc_a);
        let ba_u = d.mul(ba, u);
        let h_comm_scaled = d.congr(ab, ba, h_ab_ba, &|d, t| d.mul(t, u));
        let h_assoc_b = d.lemma(p.mul_assoc, &[b, a, u]);
        let (_end, body) = d.chain(
            lhs,
            &[
                (a_bu, h_scaled),
                (ab_u, h_assoc_a_rev),
                (ba_u, h_comm_scaled),
                (rhs, h_assoc_b),
            ],
        );
        let proof = {
            let with_bound = d.lam_fv(bound_fv, bound_ty, body);
            d.lam_fv(factor_fv, factor_ty, with_bound)
        };
        let stmt = {
            let with_bound = d.arrow(bound_ty, conclusion);
            d.arrow(factor_ty, with_bound)
        };
        (stmt, proof)
    })
    .expect("sharp witness identity checks");
    name
}

/// Close the witness equation over the factorized geometric expression. With
/// `n=k-3`, define `u=a*u'`, `q=a+u`, and `N=b*q`; ADR-0396 identifies this
/// `u` with the paper's expanded finite-sum expression.
fn admit_closed_form_sharp_witness_identity(d: &mut Dev, witness_identity: NameId) -> NameId {
    let p = d.p;
    let name = d.name("closed_form_witness_identity");
    d.theorem(name, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let two = d.num(2);
        let shifted = power_range(d, a, 1);
        let sum1 = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power1 = d.pow(a, sn);
        let twice_sum = d.mul(two, sum1);
        let tail = d.add(twice_sum, power1);
        let inner = d.add(one, tail);
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let capital_n = d.mul(b, q);

        let factor = d.refl(capital_n);
        let bound = d.lemma(p.le_add_right, &[a, u]);
        let proof = d.lemma(witness_identity, &[a, b, capital_n, q, factor, bound]);

        let ab = d.mul(a, b);
        let n_sub_ab = d.sub(capital_n, ab);
        let x = d.add(n_sub_ab, one);
        let x_sub_y = d.sub(x, one);
        let lhs = d.mul(a, x_sub_y);
        let q_sub_a = d.sub(q, a);
        let z = d.mul(a, q_sub_a);
        let rhs = d.mul(b, z);
        let stmt = d.eq(lhs, rhs);
        (stmt, proof)
    })
    .expect("closed-form sharp witness identity checks");
    name
}

#[test]
fn kernel_checks_the_exact_sharpness_factorization() {
    let mut d = Dev::new();
    let theorem = admit_sharp_factorization(&mut d);
    assert!(matches!(
        d.k.environment().get(theorem),
        Some(Declaration::Theorem { .. })
    ));

    // n=0 is the paper's k=3 empty-range corner.
    let three = d.num(3);
    let zero = d.zero();
    let proof0 = d.lemma(theorem, &[three, zero]);
    d.k.infer(proof0).expect("empty-corner application infers");

    // Nonempty anti-vacuity control: a=3,n=2 gives 156 on both sides.
    let two = d.num(2);
    let proof2 = d.lemma(theorem, &[three, two]);
    d.k.infer(proof2).expect("nonempty application infers");
    let shifted = power_range(&mut d, three, 1);
    let double_shifted = power_range(&mut d, three, 2);
    let sum1 = d.sum_range(shifted, two);
    let sum2 = d.sum_range(double_shifted, two);
    let one = d.num(1);
    let two_num = d.num(2);
    let sn = d.succ(two);
    let ssn = d.succ(sn);
    let p1 = d.pow(three, sn);
    let p2 = d.pow(three, ssn);
    let twice_sum1 = d.mul(two_num, sum1);
    let inner_tail = d.add(twice_sum1, p1);
    let inner = d.add(one, inner_tail);
    let lhs = d.mul(three, inner);
    let twice_sum2 = d.mul(two_num, sum2);
    let rhs_tail = d.add(twice_sum2, p2);
    let rhs = d.add(three, rhs_tail);
    let expected = d.num(156);
    assert!(d.k.def_eq(lhs, expected));
    assert!(d.k.def_eq(rhs, expected));

    let axioms: Vec<_> =
        d.k.environment()
            .iter()
            .filter(|(_, decl)| matches!(decl, Declaration::Axiom { .. }))
            .collect();
    assert!(axioms.is_empty(), "sharp factorization must add no axioms");
}

#[test]
fn kernel_rejects_a_broken_sharpness_factorization() {
    let mut d = Dev::new();
    let theorem = admit_sharp_factorization(&mut d);
    let two = d.num(2);
    let zero = d.zero();
    let proof = d.lemma(theorem, &[two, zero]);

    // At a=2,n=0 the checked equality is 6=6. Dropping the leading `a` from
    // the right side claims 6=4 and must not inherit the valid proof.
    let one = d.num(1);
    let power1 = d.pow(two, one);
    let inner = d.add(one, power1);
    let lhs = d.mul(two, inner);
    let power2 = d.pow(two, two);
    let false_goal = d.eq(lhs, power2);
    let bad_name = d.name("broken_factorization");
    let error =
        d.k.add_declaration(Declaration::Theorem {
            name: bad_name,
            uparams: vec![],
            ty: false_goal,
            value: proof,
        })
        .expect_err("a dropped factorization term must be rejected");
    println!("broken sharp factorization rejected: {error:?}");
    assert!(!d.k.environment().contains(bad_name));
}

#[test]
fn kernel_checks_the_quotient_free_sharpness_witness_identity() {
    let mut d = Dev::new();
    let theorem = admit_sharp_witness_identity(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let n = d.num(15);
    let q = d.num(5);
    let factor = d.refl(n);
    let three = d.num(3);
    let bound = d.lemma(d.p.le_add_right, &[a, three]);
    let proof = d.lemma(theorem, &[a, b, n, q, factor, bound]);
    d.k.infer(proof)
        .expect("quotient-free witness application infers");

    // X=10, Y=1, u=3, Z=6, hence 2*(10-1)=3*6=18.
    let ab = d.mul(a, b);
    let difference = d.sub(n, ab);
    let one = d.num(1);
    let x = d.add(difference, one);
    let x_sub_y = d.sub(x, one);
    let lhs = d.mul(a, x_sub_y);
    let u = d.sub(q, a);
    let z = d.mul(a, u);
    let rhs = d.mul(b, z);
    let eighteen = d.num(18);
    assert!(d.k.def_eq(lhs, eighteen));
    assert!(d.k.def_eq(rhs, eighteen));
}

#[test]
fn kernel_rejects_a_broken_sharpness_witness_endpoint() {
    let mut d = Dev::new();
    let theorem = admit_sharp_witness_identity(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let n = d.num(15);
    let q = d.num(5);
    let factor = d.refl(n);
    let three = d.num(3);
    let bound = d.lemma(d.p.le_add_right, &[a, three]);
    let proof = d.lemma(theorem, &[a, b, n, q, factor, bound]);

    // Dropping the `+1` from X changes X-Y from 9 to 8, so the left side is
    // 16 while bZ remains 18. The valid witness proof must not transfer.
    let ab = d.mul(a, b);
    let broken_x = d.sub(n, ab);
    let one = d.num(1);
    let broken_difference = d.sub(broken_x, one);
    let lhs = d.mul(a, broken_difference);
    let u = d.sub(q, a);
    let z = d.mul(a, u);
    let rhs = d.mul(b, z);
    let false_goal = d.eq(lhs, rhs);
    let bad_name = d.name("broken_witness_endpoint");
    let error =
        d.k.add_declaration(Declaration::Theorem {
            name: bad_name,
            uparams: vec![],
            ty: false_goal,
            value: proof,
        })
        .expect_err("a dropped witness endpoint term must be rejected");
    println!("broken sharp witness endpoint rejected: {error:?}");
    assert!(!d.k.environment().contains(bad_name));
}

#[test]
fn kernel_checks_the_closed_form_sharpness_witness_identity() {
    let mut d = Dev::new();
    let factorization = admit_sharp_factorization(&mut d);
    let witness = admit_sharp_witness_identity(&mut d);
    let closed = admit_closed_form_sharp_witness_identity(&mut d, witness);

    // The empty n=0 corner is k=3. At a=2,b=3: u=6, q=8, N=24,
    // X=19, Y=1, Z=12, and both equation sides reduce to 36.
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let proof = d.lemma(closed, &[a, b, zero]);
    d.k.infer(proof)
        .expect("closed-form empty-corner witness infers");
    let factor_proof = d.lemma(factorization, &[a, zero]);
    d.k.infer(factor_proof)
        .expect("matching empty-corner factorization infers");

    let one = d.num(1);
    let a_pow_one = d.pow(a, one);
    let inner = d.add(one, a_pow_one);
    let u = d.mul(a, inner);
    let q = d.add(a, u);
    let capital_n = d.mul(b, q);
    let ab = d.mul(a, b);
    let n_sub_ab = d.sub(capital_n, ab);
    let x = d.add(n_sub_ab, one);
    let x_sub_one = d.sub(x, one);
    let lhs = d.mul(a, x_sub_one);
    let q_sub_a = d.sub(q, a);
    let z = d.mul(a, q_sub_a);
    let rhs = d.mul(b, z);
    let thirty_six = d.num(36);
    assert!(d.k.def_eq(lhs, thirty_six));
    assert!(d.k.def_eq(rhs, thirty_six));

    let axioms: Vec<_> =
        d.k.environment()
            .iter()
            .filter(|(_, decl)| matches!(decl, Declaration::Axiom { .. }))
            .collect();
    assert!(axioms.is_empty(), "closed-form witness must add no axioms");
}

#[test]
fn kernel_rejects_a_broken_closed_form_shell_length() {
    let mut d = Dev::new();
    let witness = admit_sharp_witness_identity(&mut d);
    let closed = admit_closed_form_sharp_witness_identity(&mut d, witness);
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let proof = d.lemma(closed, &[a, b, zero]);

    // Keep q=8 but replace the checked N=24 by N=21. Then the left side is
    // 30 while bZ remains 36, so the closed-form proof must be rejected.
    let one = d.num(1);
    let a_pow_one = d.pow(a, one);
    let inner = d.add(one, a_pow_one);
    let u = d.mul(a, inner);
    let q = d.add(a, u);
    let broken_n = d.num(21);
    let ab = d.mul(a, b);
    let n_sub_ab = d.sub(broken_n, ab);
    let x = d.add(n_sub_ab, one);
    let x_sub_one = d.sub(x, one);
    let lhs = d.mul(a, x_sub_one);
    let q_sub_a = d.sub(q, a);
    let z = d.mul(a, q_sub_a);
    let rhs = d.mul(b, z);
    let false_goal = d.eq(lhs, rhs);
    let bad_name = d.name("broken_closed_form_shell_length");
    let error =
        d.k.add_declaration(Declaration::Theorem {
            name: bad_name,
            uparams: vec![],
            ty: false_goal,
            value: proof,
        })
        .expect_err("a broken closed-form shell length must be rejected");
    println!("broken closed-form shell length rejected: {error:?}");
    assert!(!d.k.environment().contains(bad_name));
}
