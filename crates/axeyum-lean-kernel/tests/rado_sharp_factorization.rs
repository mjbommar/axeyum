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
    BinderInfo, Declaration, ExprId, Kernel, NameId, NatOps, NatPrelude, NatState,
    ReducibilityHint, build_nat_prelude,
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

    fn iff_mp(&mut self, left: ExprId, right: ExprId, equivalence: ExprId) -> ExprId {
        let implication = self.arrow(left, right);
        let iff_ty = self.const_app(self.p.logic.iff, &[left, right]);
        let major_fv = self.fresh_fvar();
        let motive = self.lam_fv(major_fv, iff_ty, implication);
        let minor = {
            let mp_fv = self.fresh_fvar();
            let mp = self.k.fvar(mp_fv);
            let mpr_fv = self.fresh_fvar();
            let reverse = self.arrow(right, left);
            let with_mpr = self.lam_fv(mpr_fv, reverse, mp);
            self.lam_fv(mp_fv, implication, with_mpr)
        };
        let level_zero = self.k.level_zero();
        let rec = self.k.const_(self.p.logic.iff_rec, vec![level_zero]);
        self.apply(rec, &[left, right, motive, minor, equivalence])
    }

    fn iff_mpr(&mut self, left: ExprId, right: ExprId, equivalence: ExprId) -> ExprId {
        let implication = self.arrow(left, right);
        let reverse = self.arrow(right, left);
        let iff_ty = self.const_app(self.p.logic.iff, &[left, right]);
        let major_fv = self.fresh_fvar();
        let motive = self.lam_fv(major_fv, iff_ty, reverse);
        let minor = {
            let mp_fv = self.fresh_fvar();
            let mpr_fv = self.fresh_fvar();
            let mpr = self.k.fvar(mpr_fv);
            let with_mpr = self.lam_fv(mpr_fv, reverse, mpr);
            self.lam_fv(mp_fv, implication, with_mpr)
        };
        let level_zero = self.k.level_zero();
        let rec = self.k.const_(self.p.logic.iff_rec, vec![level_zero]);
        self.apply(rec, &[left, right, motive, minor, equivalence])
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

/// Prove the paper's closed-form witness has exact base-`a` valuation two.
/// This expands the manuscript's `u' ≡ 1 (mod a)` sentence into a checked
/// factorization of the shifted sum and final power by `a`.
fn admit_closed_form_witness_valuation(d: &mut Dev) -> NameId {
    let p = d.p;
    let name = d.name("closed_form_witness_valuation");
    d.theorem(name, 3, &|d, v| {
        let (a, _b, n) = (v[0], v[1], v[2]);
        let two = d.num(2);
        let bound_ty = d.le(two, a);
        let bound_fv = d.fresh_fvar();
        let bound = d.k.fvar(bound_fv);
        let one = d.num(1);

        let unshifted = power_range(d, a, 0);
        let shifted = power_range(d, a, 1);
        let sum0 = d.sum_range(unshifted, n);
        let sum1 = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power_n = d.pow(a, n);
        let power1 = d.pow(a, sn);
        let twice_sum1 = d.mul(two, sum1);
        let tail = d.add(twice_sum1, power1);
        let inner = d.add(one, tail);

        // sum1 = a*sum0.
        let a_sum0 = d.mul(a, sum0);
        let a_sum0_eq_sum1 = d.lemma(p.mul_sum_range_pow, &[a, n]);
        let sum1_eq_a_sum0 = d.symm(a_sum0, sum1, a_sum0_eq_sum1);

        // 2*sum1 = a*(2*sum0).
        let two_a_sum0 = d.mul(two, a_sum0);
        let h_sum_under_two = d.congr(sum1, a_sum0, sum1_eq_a_sum0, &|d, x| d.mul(two, x));
        let two_a = d.mul(two, a);
        let two_a_times_sum0 = d.mul(two_a, sum0);
        let h_assoc_two = d.lemma(p.mul_assoc, &[two, a, sum0]);
        let h_assoc_two_rev = d.symm(two_a_times_sum0, two_a_sum0, h_assoc_two);
        let a_two = d.mul(a, two);
        let a_two_times_sum0 = d.mul(a_two, sum0);
        let h_two_a = d.lemma(p.mul_comm, &[two, a]);
        let h_comm_under_sum = d.congr(two_a, a_two, h_two_a, &|d, x| d.mul(x, sum0));
        let twice_sum0 = d.mul(two, sum0);
        let a_twice_sum0 = d.mul(a, twice_sum0);
        let h_assoc_a = d.lemma(p.mul_assoc, &[a, two, sum0]);
        let (_, twice_sum1_eq_factored) = d.chain(
            twice_sum1,
            &[
                (two_a_sum0, h_sum_under_two),
                (two_a_times_sum0, h_assoc_two_rev),
                (a_two_times_sum0, h_comm_under_sum),
                (a_twice_sum0, h_assoc_a),
            ],
        );

        // a^(n+1) = a*a^n.
        let power_n_a = d.mul(power_n, a);
        let a_power_n = d.mul(a, power_n);
        let h_power = d.lemma(p.pow_succ, &[a, n]);
        let h_power_comm = d.lemma(p.mul_comm, &[power_n, a]);
        let (_, power1_eq_factored) =
            d.chain(power1, &[(power_n_a, h_power), (a_power_n, h_power_comm)]);

        let factored_terms = d.add(a_twice_sum0, a_power_n);
        let t = d.add(twice_sum0, power_n);
        let a_t = d.mul(a, t);
        let h_tail_left = d.congr(twice_sum1, a_twice_sum0, twice_sum1_eq_factored, &|d, x| {
            d.add(x, power1)
        });
        let h_tail_right = d.congr(power1, a_power_n, power1_eq_factored, &|d, x| {
            d.add(a_twice_sum0, x)
        });
        let h_distribute = d.lemma(p.left_distrib, &[a, twice_sum0, power_n]);
        let h_distribute_rev = d.symm(a_t, factored_terms, h_distribute);
        let factored_left = d.add(a_twice_sum0, power1);
        let (_, tail_eq_a_t) = d.chain(
            tail,
            &[
                (factored_left, h_tail_left),
                (factored_terms, h_tail_right),
                (a_t, h_distribute_rev),
            ],
        );

        let shaped_inner = d.add(one, a_t);
        let inner_eq_shaped = d.congr(tail, a_t, tail_eq_a_t, &|d, x| d.add(one, x));
        let shaped_not_dvd = d.lemma(p.not_dvd_one_add_mul_of_two_le, &[a, t, bound]);
        let shaped_eq_inner = d.symm(inner, shaped_inner, inner_eq_shaped);
        let inner_not_dvd = {
            let motive = d.eq_motive(shaped_inner, &|d, x| {
                let divides = d.dvd(a, x);
                d.const_app(p.logic.not, &[divides])
            });
            d.transport(shaped_inner, motive, shaped_not_dvd, inner, shaped_eq_inner)
        };

        let aa = d.mul(a, a);
        let aa_inner = d.mul(aa, inner);
        let generic = d.lemma(p.valuation_at_two_mul_sq, &[a, inner, bound, inner_not_dvd]);

        // Return to the witness as stated: q=a+a*inner and Z=a*(q-a).
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let q_sub_a = d.sub(q, a);
        let restored = d.add(q_sub_a, a);
        let a_le_q = d.lemma(p.le_add_right, &[a, u]);
        let restored_eq_q = d.lemma(p.sub_add_cancel, &[a, q, a_le_q]);
        let u_plus_a = d.add(u, a);
        let q_eq_u_plus_a = d.lemma(p.add_comm, &[a, u]);
        let (_, common_sum) = d.chain(restored, &[(q, restored_eq_q), (u_plus_a, q_eq_u_plus_a)]);
        let q_sub_a_eq_u = d.lemma(p.add_right_cancel, &[q_sub_a, u, a, common_sum]);
        let z = d.mul(a, q_sub_a);
        let a_u = d.mul(a, u);
        let z_eq_a_u = d.congr(q_sub_a, u, q_sub_a_eq_u, &|d, x| d.mul(a, x));
        let h_assoc = d.lemma(p.mul_assoc, &[a, a, inner]);
        let a_u_eq_aa_inner = d.symm(aa_inner, a_u, h_assoc);
        let (_, z_eq_aa_inner) = d.chain(z, &[(a_u, z_eq_a_u), (aa_inner, a_u_eq_aa_inner)]);
        let aa_inner_eq_z = d.symm(z, aa_inner, z_eq_aa_inner);
        let body = {
            let motive = d.eq_motive(aa_inner, &|d, value| d.valuation_at(a, value, two));
            d.transport(aa_inner, motive, generic, z, aa_inner_eq_z)
        };
        let conclusion = d.valuation_at(a, z, two);
        let stmt = d.arrow(bound_ty, conclusion);
        let proof = d.lam_fv(bound_fv, bound_ty, body);
        (stmt, proof)
    })
    .expect("closed-form witness valuation checks");
    name
}

#[derive(Clone, Copy)]
struct RangeTheorems {
    x_lower: NameId,
    y_upper: NameId,
    x_upper: NameId,
    z_lower: NameId,
    z_upper_if_a_le_b: NameId,
}

#[derive(Clone, Copy)]
struct ColourTwoDefinitions {
    shell_two_member: NameId,
    colour_two_at: NameId,
}

fn define_colour_two_relations(d: &mut Dev) -> ColourTwoDefinitions {
    let p = d.p;
    let nat = d.nat_ty();
    let prop = d.k.sort_zero();
    let anon = d.k.anon();

    let shell_two_member = d.name("shellTwoMember");
    {
        let n_fv = d.fresh_fvar();
        let capital_n = d.k.fvar(n_fv);
        let ab_fv = d.fresh_fvar();
        let ab = d.k.fvar(ab_fv);
        let value_fv = d.fresh_fvar();
        let value = d.k.fvar(value_fv);
        let one = d.num(1);
        let left = d.in_closed_interval(one, ab, value);
        let difference = d.sub(capital_n, ab);
        let right_lower = d.add(difference, one);
        let right = d.in_closed_interval(right_lower, capital_n, value);
        let body = d.const_app(p.logic.or, &[left, right]);
        let value = {
            let with_value = d.lam_fv(value_fv, nat, body);
            let with_ab = d.lam_fv(ab_fv, nat, with_value);
            d.lam_fv(n_fv, nat, with_ab)
        };
        let ty = {
            let with_value = d.k.pi(anon, nat, prop, BinderInfo::Default);
            let with_ab = d.k.pi(anon, nat, with_value, BinderInfo::Default);
            d.k.pi(anon, nat, with_ab, BinderInfo::Default)
        };
        d.k.add_declaration(Declaration::Definition {
            name: shell_two_member,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })
        .expect("shell-two membership definition checks");
    }

    let colour_two_at = d.name("colourTwoAt");
    {
        let a_fv = d.fresh_fvar();
        let a = d.k.fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let capital_n = d.k.fvar(n_fv);
        let ab_fv = d.fresh_fvar();
        let ab = d.k.fvar(ab_fv);
        let value_fv = d.fresh_fvar();
        let value = d.k.fvar(value_fv);
        let one = d.num(1);
        let two = d.num(2);
        let domain = d.in_closed_interval(one, capital_n, value);
        let valuation = d.valuation_at(a, value, two);
        let divides = d.dvd(a, value);
        let unit = d.const_app(p.logic.not, &[divides]);
        let shell = d.const_app(shell_two_member, &[capital_n, ab, value]);
        let unit_in_shell = d.const_app(p.logic.and, &[unit, shell]);
        let classified = d.const_app(p.logic.or, &[valuation, unit_in_shell]);
        let body = d.const_app(p.logic.and, &[domain, classified]);
        let value = {
            let with_value = d.lam_fv(value_fv, nat, body);
            let with_ab = d.lam_fv(ab_fv, nat, with_value);
            let with_n = d.lam_fv(n_fv, nat, with_ab);
            d.lam_fv(a_fv, nat, with_n)
        };
        let ty = {
            let with_value = d.k.pi(anon, nat, prop, BinderInfo::Default);
            let with_ab = d.k.pi(anon, nat, with_value, BinderInfo::Default);
            let with_n = d.k.pi(anon, nat, with_ab, BinderInfo::Default);
            d.k.pi(anon, nat, with_n, BinderInfo::Default)
        };
        d.k.add_declaration(Declaration::Definition {
            name: colour_two_at,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(7),
        })
        .expect("colour-two relation checks");
    }

    ColourTwoDefinitions {
        shell_two_member,
        colour_two_at,
    }
}

fn shell_two_member(
    d: &mut Dev,
    defs: ColourTwoDefinitions,
    capital_n: ExprId,
    ab: ExprId,
    value: ExprId,
) -> ExprId {
    d.const_app(defs.shell_two_member, &[capital_n, ab, value])
}

fn colour_two_at(
    d: &mut Dev,
    defs: ColourTwoDefinitions,
    a: ExprId,
    capital_n: ExprId,
    ab: ExprId,
    value: ExprId,
) -> ExprId {
    d.const_app(defs.colour_two_at, &[a, capital_n, ab, value])
}

/// Admit the exact signed-range criterion from the paper in Nat form:
///
/// `a*(q-a) <= N  <->  N*(a-b) <= a^2*b`,
///
/// under `N=b*q`, `a<=q`, and `1<=b`. Nat subtraction encodes the paper's
/// signed case split: when `a<=b`, `a-b=0`; when `b<=a`, subtraction
/// distribution and order adjunction recover the displayed integer algebra.
fn admit_exact_range_criterion(d: &mut Dev) -> NameId {
    let p = d.p;
    let name = d.name("exact_range_criterion");
    d.theorem(name, 4, &|d, v| {
        let (a, b, capital_n, q) = (v[0], v[1], v[2], v[3]);
        let bq = d.mul(b, q);
        let factor_ty = d.eq(capital_n, bq);
        let factor_fv = d.fresh_fvar();
        let factor = d.k.fvar(factor_fv);
        let a_le_q_ty = d.le(a, q);
        let a_le_q_fv = d.fresh_fvar();
        let a_le_q = d.k.fvar(a_le_q_fv);
        let one = d.num(1);
        let positive_ty = d.le(one, b);
        let positive_fv = d.fresh_fvar();
        let positive = d.k.fvar(positive_fv);

        let u = d.sub(q, a);
        let z = d.mul(a, u);
        let range = d.le(z, capital_n);
        let a_sub_b = d.sub(a, b);
        let criterion_lhs = d.mul(capital_n, a_sub_b);
        let aa = d.mul(a, a);
        let square_b = d.mul(aa, b);
        let criterion = d.le(criterion_lhs, square_b);
        let conclusion = d.const_app(p.logic.iff, &[range, criterion]);

        let a_le_b = d.le(a, b);
        let b_le_a = d.le(b, a);
        let total = d.lemma(p.le_total, &[a, b]);
        let total_ty = d.const_app(p.logic.or, &[a_le_b, b_le_a]);
        let motive_fv = d.fresh_fvar();
        let motive = d.lam_fv(motive_fv, total_ty, conclusion);

        let a_le_b_minor = {
            let hab_fv = d.fresh_fvar();
            let hab = d.k.fvar(hab_fv);

            let restored = d.add(u, a);
            let restored_eq_q = d.lemma(p.sub_add_cancel, &[a, q, a_le_q]);
            let u_le_restored = d.lemma(p.le_add_right, &[u, a]);
            let u_le_q = transport_le_upper(d, u, restored, q, u_le_restored, restored_eq_q);
            let au = z;
            let aq = d.mul(a, q);
            let au_le_aq = d.lemma(p.mul_le_mul_left, &[a, u, q, u_le_q]);
            let qa = d.mul(q, a);
            let qb = d.mul(q, b);
            let qa_le_qb = d.lemma(p.mul_le_mul_left, &[q, a, b, hab]);
            let qa_eq_aq = d.lemma(p.mul_comm, &[q, a]);
            let aq_le_qb = transport_le_lower(d, qa, aq, qb, qa_le_qb, qa_eq_aq);
            let qb_eq_bq = d.lemma(p.mul_comm, &[q, b]);
            let aq_le_bq = transport_le_upper(d, aq, qb, bq, aq_le_qb, qb_eq_bq);
            let bq_eq_n = d.symm(capital_n, bq, factor);
            let aq_le_n = transport_le_upper(d, aq, bq, capital_n, aq_le_bq, bq_eq_n);
            let range_proof = d.lemma(p.le_trans, &[au, aq, capital_n, au_le_aq, aq_le_n]);

            let zero = d.zero();
            let difference_eq_zero = d.lemma(p.sub_eq_zero_of_le, &[a, b, hab]);
            let n_zero = d.mul(capital_n, zero);
            let lhs_eq_n_zero = d.congr(a_sub_b, zero, difference_eq_zero, &|d, x| {
                d.mul(capital_n, x)
            });
            let n_zero_eq_zero = d.lemma(p.mul_zero, &[capital_n]);
            let (_, lhs_eq_zero) = d.chain(
                criterion_lhs,
                &[(n_zero, lhs_eq_n_zero), (zero, n_zero_eq_zero)],
            );
            let zero_le_square = d.lemma(p.zero_le, &[square_b]);
            let zero_eq_lhs = d.symm(criterion_lhs, zero, lhs_eq_zero);
            let criterion_proof = transport_le_lower(
                d,
                zero,
                criterion_lhs,
                square_b,
                zero_le_square,
                zero_eq_lhs,
            );

            let mp_fv = d.fresh_fvar();
            let mp = d.lam_fv(mp_fv, range, criterion_proof);
            let mpr_fv = d.fresh_fvar();
            let mpr = d.lam_fv(mpr_fv, criterion, range_proof);
            let body = d.const_app(p.logic.iff_intro, &[range, criterion, mp, mpr]);
            d.lam_fv(hab_fv, a_le_b, body)
        };

        let b_le_a_minor = {
            let hba_fv = d.fresh_fvar();
            let hba = d.k.fvar(hba_fv);
            let bz = d.mul(b, z);
            let ba = d.mul(b, a);
            let ab = d.mul(a, b);
            let ba_u = d.mul(ba, u);
            let ab_u = d.mul(ab, u);
            let ab_q = d.mul(ab, q);
            let ab_a = d.mul(ab, a);
            let algebraic_difference = d.sub(ab_q, ab_a);

            let h_assoc_b = d.lemma(p.mul_assoc, &[b, a, u]);
            let bz_eq_ba_u = d.symm(ba_u, bz, h_assoc_b);
            let ba_eq_ab = d.lemma(p.mul_comm, &[b, a]);
            let ba_u_eq_ab_u = d.congr(ba, ab, ba_eq_ab, &|d, x| d.mul(x, u));
            let ab_u_eq_difference = d.lemma(p.mul_sub_left_distrib, &[ab, q, a, a_le_q]);

            let a_bq = d.mul(a, bq);
            let a_n = d.mul(a, capital_n);
            let ab_q_eq_a_bq = d.lemma(p.mul_assoc, &[a, b, q]);
            let bq_eq_n = d.symm(capital_n, bq, factor);
            let a_bq_eq_a_n = d.congr(bq, capital_n, bq_eq_n, &|d, x| d.mul(a, x));
            let (_, ab_q_eq_a_n) = d.chain(ab_q, &[(a_bq, ab_q_eq_a_bq), (a_n, a_bq_eq_a_n)]);

            let a_ba = d.mul(a, ba);
            let a_ab = d.mul(a, ab);
            let aa_b = square_b;
            let ab_a_eq_a_ba = d.lemma(p.mul_assoc, &[a, b, a]);
            let a_ba_eq_a_ab = d.congr(ba, ab, ba_eq_ab, &|d, x| d.mul(a, x));
            let aa_b_eq_a_ab = d.lemma(p.mul_assoc, &[a, a, b]);
            let a_ab_eq_aa_b = d.symm(aa_b, a_ab, aa_b_eq_a_ab);
            let (_, ab_a_eq_aa_b) = d.chain(
                ab_a,
                &[
                    (a_ba, ab_a_eq_a_ba),
                    (a_ab, a_ba_eq_a_ab),
                    (aa_b, a_ab_eq_aa_b),
                ],
            );

            let a_n_sub_ab_a = d.sub(a_n, ab_a);
            let exact_difference = d.sub(a_n, square_b);
            let h_first = d.congr(ab_q, a_n, ab_q_eq_a_n, &|d, x| d.sub(x, ab_a));
            let h_second = d.congr(ab_a, square_b, ab_a_eq_aa_b, &|d, x| d.sub(a_n, x));
            let (_, bz_eq_difference) = d.chain(
                bz,
                &[
                    (ba_u, bz_eq_ba_u),
                    (ab_u, ba_u_eq_ab_u),
                    (algebraic_difference, ab_u_eq_difference),
                    (a_n_sub_ab_a, h_first),
                    (exact_difference, h_second),
                ],
            );

            let b_n = d.mul(b, capital_n);
            let n_a = d.mul(capital_n, a);
            let n_b = d.mul(capital_n, b);
            let additive_left = d.add(b_n, square_b);
            let additive_right = d.add(square_b, n_b);
            let a_n_eq_n_a = d.lemma(p.mul_comm, &[a, capital_n]);
            let b_n_eq_n_b = d.lemma(p.mul_comm, &[b, capital_n]);
            let swapped = d.add(square_b, b_n);
            let additive_left_eq_swapped = d.lemma(p.add_comm, &[b_n, square_b]);
            let swapped_eq_right = d.congr(b_n, n_b, b_n_eq_n_b, &|d, x| d.add(square_b, x));
            let (_, additive_left_eq_right) = d.chain(
                additive_left,
                &[
                    (swapped, additive_left_eq_swapped),
                    (additive_right, swapped_eq_right),
                ],
            );

            let first_adj = d.lemma(p.sub_le_iff_le_add, &[a_n, square_b, b_n]);
            let first_left = d.le(exact_difference, b_n);
            let first_right = d.le(a_n, additive_left);
            let second_difference = d.sub(n_a, n_b);
            let second_left = d.le(second_difference, square_b);
            let second_right = d.le(n_a, additive_right);
            let second_adj = d.lemma(p.sub_le_iff_le_add, &[n_a, n_b, square_b]);
            let distributed = d.lemma(p.mul_sub_left_distrib, &[capital_n, a, b, hba]);

            let mp = {
                let h_fv = d.fresh_fvar();
                let h = d.k.fvar(h_fv);
                let scaled = d.lemma(p.mul_le_mul_left, &[b, z, capital_n, h]);
                let difference_bound =
                    transport_le_lower(d, bz, exact_difference, b_n, scaled, bz_eq_difference);
                let first_mp = d.iff_mp(first_left, first_right, first_adj);
                let original_additive = d.apply(first_mp, &[difference_bound]);
                let lower_motive = d.eq_motive(a_n, &|d, lower| d.le(lower, additive_left));
                let commuted_lower =
                    d.transport(a_n, lower_motive, original_additive, n_a, a_n_eq_n_a);
                let upper_motive = d.eq_motive(additive_left, &|d, upper| d.le(n_a, upper));
                let commuted = d.transport(
                    additive_left,
                    upper_motive,
                    commuted_lower,
                    additive_right,
                    additive_left_eq_right,
                );
                let second_mpr = d.iff_mpr(second_left, second_right, second_adj);
                let difference_bound = d.apply(second_mpr, &[commuted]);
                let difference_eq_lhs = d.symm(criterion_lhs, second_difference, distributed);
                let body = transport_le_lower(
                    d,
                    second_difference,
                    criterion_lhs,
                    square_b,
                    difference_bound,
                    difference_eq_lhs,
                );
                d.lam_fv(h_fv, range, body)
            };

            let mpr = {
                let h_fv = d.fresh_fvar();
                let h = d.k.fvar(h_fv);
                let lhs_eq_difference = distributed;
                let difference_bound = transport_le_lower(
                    d,
                    criterion_lhs,
                    second_difference,
                    square_b,
                    h,
                    lhs_eq_difference,
                );
                let second_mp = d.iff_mp(second_left, second_right, second_adj);
                let commuted = d.apply(second_mp, &[difference_bound]);
                let n_a_eq_a_n = d.symm(a_n, n_a, a_n_eq_n_a);
                let right_eq_left = d.symm(additive_left, additive_right, additive_left_eq_right);
                let lower_motive = d.eq_motive(n_a, &|d, lower| d.le(lower, additive_right));
                let original_lower = d.transport(n_a, lower_motive, commuted, a_n, n_a_eq_a_n);
                let upper_motive = d.eq_motive(additive_right, &|d, upper| d.le(a_n, upper));
                let original_additive = d.transport(
                    additive_right,
                    upper_motive,
                    original_lower,
                    additive_left,
                    right_eq_left,
                );
                let first_mpr = d.iff_mpr(first_left, first_right, first_adj);
                let exact_bound = d.apply(first_mpr, &[original_additive]);
                let difference_eq_bz = d.symm(bz, exact_difference, bz_eq_difference);
                let scaled =
                    transport_le_lower(d, exact_difference, bz, b_n, exact_bound, difference_eq_bz);
                let body = d.lemma(
                    p.le_of_mul_le_mul_left,
                    &[b, z, capital_n, positive, scaled],
                );
                d.lam_fv(h_fv, criterion, body)
            };

            let body = d.const_app(p.logic.iff_intro, &[range, criterion, mp, mpr]);
            d.lam_fv(hba_fv, b_le_a, body)
        };

        let or_rec = d.k.const_(p.logic.or_rec, vec![]);
        let body = d.apply(
            or_rec,
            &[a_le_b, b_le_a, motive, a_le_b_minor, b_le_a_minor, total],
        );
        let proof = {
            let with_positive = d.lam_fv(positive_fv, positive_ty, body);
            let with_bound = d.lam_fv(a_le_q_fv, a_le_q_ty, with_positive);
            d.lam_fv(factor_fv, factor_ty, with_bound)
        };
        let stmt = {
            let with_positive = d.arrow(positive_ty, conclusion);
            let with_bound = d.arrow(a_le_q_ty, with_positive);
            d.arrow(factor_ty, with_bound)
        };
        (stmt, proof)
    })
    .expect("exact Rado range criterion checks");
    name
}

/// Specialize the exact criterion to the paper's closed-form shell witness.
fn admit_closed_form_exact_range_criterion(d: &mut Dev, exact: NameId) -> NameId {
    let p = d.p;
    let name = d.name("closed_form_exact_range_criterion");
    d.theorem(name, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let positive_ty = d.le(one, b);
        let positive_fv = d.fresh_fvar();
        let positive = d.k.fvar(positive_fv);

        let two = d.num(2);
        let shifted = power_range(d, a, 1);
        let sum = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power = d.pow(a, sn);
        let twice_sum = d.mul(two, sum);
        let tail = d.add(twice_sum, power);
        let inner = d.add(one, tail);
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let capital_n = d.mul(b, q);
        let factor = d.refl(capital_n);
        let a_le_q = d.lemma(p.le_add_right, &[a, u]);
        let body = d.lemma(exact, &[a, b, capital_n, q, factor, a_le_q, positive]);

        let q_sub_a = d.sub(q, a);
        let z = d.mul(a, q_sub_a);
        let range = d.le(z, capital_n);
        let a_sub_b = d.sub(a, b);
        let criterion_lhs = d.mul(capital_n, a_sub_b);
        let aa = d.mul(a, a);
        let square_b = d.mul(aa, b);
        let criterion = d.le(criterion_lhs, square_b);
        let conclusion = d.const_app(p.logic.iff, &[range, criterion]);
        let stmt = d.arrow(positive_ty, conclusion);
        let proof = d.lam_fv(positive_fv, positive_ty, body);
        (stmt, proof)
    })
    .expect("closed-form exact Rado range criterion checks");
    name
}

fn transport_le_upper(
    d: &mut Dev,
    lower: ExprId,
    from: ExprId,
    to: ExprId,
    bound: ExprId,
    equality: ExprId,
) -> ExprId {
    let motive = d.eq_motive(from, &|d, x| d.le(lower, x));
    d.transport(from, motive, bound, to, equality)
}

fn transport_le_lower(
    d: &mut Dev,
    from: ExprId,
    to: ExprId,
    upper: ExprId,
    bound: ExprId,
    equality: ExprId,
) -> ExprId {
    let motive = d.eq_motive(from, &|d, x| d.le(x, upper));
    d.transport(from, motive, bound, to, equality)
}

/// Admit the unconditional range facts for the closed-form witness. The upper
/// bound `Z <= N` is deliberately not manufactured here: it is the paper's
/// signed side condition and remains an explicit hypothesis for membership.
fn admit_closed_form_range_theorems(d: &mut Dev) -> RangeTheorems {
    let p = d.p;

    let x_lower = d.name("closed_form_x_lower");
    d.theorem(x_lower, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let two = d.num(2);
        let shifted = power_range(d, a, 1);
        let sum = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power = d.pow(a, sn);
        let twice_sum = d.mul(two, sum);
        let tail = d.add(twice_sum, power);
        let inner = d.add(one, tail);
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let capital_n = d.mul(b, q);
        let ab = d.mul(a, b);
        let difference = d.sub(capital_n, ab);
        let x = d.add(difference, one);
        let zero = d.zero();
        let zero_le_difference = d.lemma(p.zero_le, &[difference]);
        let proof = d.lemma(p.le_succ_succ, &[zero, difference, zero_le_difference]);
        (d.le(one, x), proof)
    })
    .expect("closed-form X lower bound checks");

    let y_upper = d.name("closed_form_y_upper");
    d.theorem(y_upper, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let ha_ty = d.le(one, a);
        let ha_fv = d.fresh_fvar();
        let ha = d.k.fvar(ha_fv);
        let hb_ty = d.le(one, b);
        let hb_fv = d.fresh_fvar();
        let hb = d.k.fvar(hb_fv);
        let two = d.num(2);
        let shifted = power_range(d, a, 1);
        let sum = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power = d.pow(a, sn);
        let twice_sum = d.mul(two, sum);
        let tail = d.add(twice_sum, power);
        let inner = d.add(one, tail);
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let capital_n = d.mul(b, q);
        let a_le_q = d.lemma(p.le_add_right, &[a, u]);
        let one_le_q = d.lemma(p.le_trans, &[one, a, q, ha, a_le_q]);
        let b_times_one = d.mul(b, one);
        let b_times_one_le_n = d.lemma(p.mul_le_mul_left, &[b, one, q, one_le_q]);
        let b_times_one_eq_b = d.lemma(p.mul_one, &[b]);
        let b_le_n = transport_le_lower(
            d,
            b_times_one,
            b,
            capital_n,
            b_times_one_le_n,
            b_times_one_eq_b,
        );
        let body = d.lemma(p.le_trans, &[one, b, capital_n, hb, b_le_n]);
        let conclusion = d.le(one, capital_n);
        let proof = {
            let with_hb = d.lam_fv(hb_fv, hb_ty, body);
            d.lam_fv(ha_fv, ha_ty, with_hb)
        };
        let stmt = {
            let with_hb = d.arrow(hb_ty, conclusion);
            d.arrow(ha_ty, with_hb)
        };
        (stmt, proof)
    })
    .expect("closed-form Y upper bound checks");

    let x_upper = d.name("closed_form_x_upper");
    d.theorem(x_upper, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let ha_ty = d.le(one, a);
        let ha_fv = d.fresh_fvar();
        let ha = d.k.fvar(ha_fv);
        let hb_ty = d.le(one, b);
        let hb_fv = d.fresh_fvar();
        let hb = d.k.fvar(hb_fv);
        let two = d.num(2);
        let shifted = power_range(d, a, 1);
        let sum = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power = d.pow(a, sn);
        let twice_sum = d.mul(two, sum);
        let tail = d.add(twice_sum, power);
        let inner = d.add(one, tail);
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let capital_n = d.mul(b, q);
        let ab = d.mul(a, b);
        let ba = d.mul(b, a);

        let a_le_q = d.lemma(p.le_add_right, &[a, u]);
        let ba_le_n = d.lemma(p.mul_le_mul_left, &[b, a, q, a_le_q]);
        let ab_eq_ba = d.lemma(p.mul_comm, &[a, b]);
        let ba_eq_ab = d.symm(ab, ba, ab_eq_ba);
        let ab_le_n = transport_le_lower(d, ba, ab, capital_n, ba_le_n, ba_eq_ab);
        let difference = d.sub(capital_n, ab);
        let restored = d.add(difference, ab);
        let restored_eq_n = d.lemma(p.sub_add_cancel, &[ab, capital_n, ab_le_n]);

        let a_times_one = d.mul(a, one);
        let a_times_one_le_ab = d.lemma(p.mul_le_mul_left, &[a, one, b, hb]);
        let a_times_one_eq_a = d.lemma(p.mul_one, &[a]);
        let a_le_ab =
            transport_le_lower(d, a_times_one, a, ab, a_times_one_le_ab, a_times_one_eq_a);
        let one_le_ab = d.lemma(p.le_trans, &[one, a, ab, ha, a_le_ab]);
        let x = d.add(difference, one);
        let x_le_restored = d.lemma(p.add_le_add_left, &[difference, one, ab, one_le_ab]);
        let body = transport_le_upper(d, x, restored, capital_n, x_le_restored, restored_eq_n);
        let conclusion = d.le(x, capital_n);
        let proof = {
            let with_hb = d.lam_fv(hb_fv, hb_ty, body);
            d.lam_fv(ha_fv, ha_ty, with_hb)
        };
        let stmt = {
            let with_hb = d.arrow(hb_ty, conclusion);
            d.arrow(ha_ty, with_hb)
        };
        (stmt, proof)
    })
    .expect("closed-form X upper bound checks");

    let z_lower = d.name("closed_form_z_lower");
    d.theorem(z_lower, 3, &|d, v| {
        let (a, _b, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let ha_ty = d.le(one, a);
        let ha_fv = d.fresh_fvar();
        let ha = d.k.fvar(ha_fv);
        let two = d.num(2);
        let shifted = power_range(d, a, 1);
        let sum = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power = d.pow(a, sn);
        let twice_sum = d.mul(two, sum);
        let tail = d.add(twice_sum, power);
        let inner = d.add(one, tail);
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let one_le_inner = d.lemma(p.le_add_right, &[one, tail]);
        let a_times_one = d.mul(a, one);
        let a_times_one_eq_a = d.lemma(p.mul_one, &[a]);
        let a_times_one_le_u = d.lemma(p.mul_le_mul_left, &[a, one, inner, one_le_inner]);
        let a_le_u = transport_le_lower(d, a_times_one, a, u, a_times_one_le_u, a_times_one_eq_a);
        let one_le_u = d.lemma(p.le_trans, &[one, a, u, ha, a_le_u]);
        let au = d.mul(a, u);
        let a_times_one_le_au = d.lemma(p.mul_le_mul_left, &[a, one, u, one_le_u]);
        let a_le_au =
            transport_le_lower(d, a_times_one, a, au, a_times_one_le_au, a_times_one_eq_a);
        let one_le_au = d.lemma(p.le_trans, &[one, a, au, ha, a_le_au]);

        let q_sub_a = d.sub(q, a);
        let restored = d.add(q_sub_a, a);
        let a_le_q = d.lemma(p.le_add_right, &[a, u]);
        let restored_eq_q = d.lemma(p.sub_add_cancel, &[a, q, a_le_q]);
        let u_plus_a = d.add(u, a);
        let q_eq_u_plus_a = d.lemma(p.add_comm, &[a, u]);
        let (_end, common_sum) =
            d.chain(restored, &[(q, restored_eq_q), (u_plus_a, q_eq_u_plus_a)]);
        let sub_eq_u = d.lemma(p.add_right_cancel, &[q_sub_a, u, a, common_sum]);
        let z = d.mul(a, q_sub_a);
        let z_eq_au = d.congr(q_sub_a, u, sub_eq_u, &|d, x| d.mul(a, x));
        let au_eq_z = d.symm(z, au, z_eq_au);
        let body = transport_le_upper(d, one, au, z, one_le_au, au_eq_z);
        let conclusion = d.le(one, z);
        let stmt = d.arrow(ha_ty, conclusion);
        let proof = d.lam_fv(ha_fv, ha_ty, body);
        (stmt, proof)
    })
    .expect("closed-form Z lower bound checks");

    let z_upper_if_a_le_b = d.name("closed_form_z_upper_if_a_le_b");
    d.theorem(z_upper_if_a_le_b, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let hab_ty = d.le(a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.k.fvar(hab_fv);
        let one = d.num(1);
        let two = d.num(2);
        let shifted = power_range(d, a, 1);
        let sum = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power = d.pow(a, sn);
        let twice_sum = d.mul(two, sum);
        let tail = d.add(twice_sum, power);
        let inner = d.add(one, tail);
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let capital_n = d.mul(b, q);

        let u_plus_a = d.add(u, a);
        let u_le_u_plus_a = d.lemma(p.le_add_right, &[u, a]);
        let q_eq_u_plus_a = d.lemma(p.add_comm, &[a, u]);
        let u_plus_a_eq_q = d.symm(q, u_plus_a, q_eq_u_plus_a);
        let u_le_q = transport_le_upper(d, u, u_plus_a, q, u_le_u_plus_a, u_plus_a_eq_q);
        let au = d.mul(a, u);
        let aq = d.mul(a, q);
        let au_le_aq = d.lemma(p.mul_le_mul_left, &[a, u, q, u_le_q]);

        let qa = d.mul(q, a);
        let qb = d.mul(q, b);
        let qa_le_qb = d.lemma(p.mul_le_mul_left, &[q, a, b, hab]);
        let qa_eq_aq = d.lemma(p.mul_comm, &[q, a]);
        let aq_le_qb = transport_le_lower(d, qa, aq, qb, qa_le_qb, qa_eq_aq);
        let qb_eq_n = d.lemma(p.mul_comm, &[q, b]);
        let aq_le_n = transport_le_upper(d, aq, qb, capital_n, aq_le_qb, qb_eq_n);
        let au_le_n = d.lemma(p.le_trans, &[au, aq, capital_n, au_le_aq, aq_le_n]);

        let q_sub_a = d.sub(q, a);
        let restored = d.add(q_sub_a, a);
        let a_le_q = d.lemma(p.le_add_right, &[a, u]);
        let restored_eq_q = d.lemma(p.sub_add_cancel, &[a, q, a_le_q]);
        let (_end, common_sum) =
            d.chain(restored, &[(q, restored_eq_q), (u_plus_a, q_eq_u_plus_a)]);
        let sub_eq_u = d.lemma(p.add_right_cancel, &[q_sub_a, u, a, common_sum]);
        let z = d.mul(a, q_sub_a);
        let z_eq_au = d.congr(q_sub_a, u, sub_eq_u, &|d, x| d.mul(a, x));
        let au_eq_z = d.symm(z, au, z_eq_au);
        let body = transport_le_lower(d, au, z, capital_n, au_le_n, au_eq_z);
        let conclusion = d.le(z, capital_n);
        let stmt = d.arrow(hab_ty, conclusion);
        let proof = d.lam_fv(hab_fv, hab_ty, body);
        (stmt, proof)
    })
    .expect("closed-form Z upper bound checks when a <= b");

    RangeTheorems {
        x_lower,
        y_upper,
        x_upper,
        z_lower,
        z_upper_if_a_le_b,
    }
}

/// Prove that the three closed-form witness terms all have manuscript colour
/// two. The relation includes membership in `[1,N]`; consequently the paper's
/// explicit `Z <= N` guard remains an explicit theorem hypothesis.
fn admit_closed_form_witness_colour_two(
    d: &mut Dev,
    defs: ColourTwoDefinitions,
    ranges: RangeTheorems,
    valuation: NameId,
) -> NameId {
    let p = d.p;
    let name = d.name("closed_form_witness_colour_two");
    d.theorem(name, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let two = d.num(2);
        let ha_two_ty = d.le(two, a);
        let ha_two_fv = d.fresh_fvar();
        let ha_two = d.k.fvar(ha_two_fv);
        let hb_ty = d.le(one, b);
        let hb_fv = d.fresh_fvar();
        let hb = d.k.fvar(hb_fv);

        let shifted = power_range(d, a, 1);
        let sum = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power = d.pow(a, sn);
        let twice_sum = d.mul(two, sum);
        let tail = d.add(twice_sum, power);
        let inner = d.add(one, tail);
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let capital_n = d.mul(b, q);
        let ab = d.mul(a, b);
        let difference = d.sub(capital_n, ab);
        let x = d.add(difference, one);
        let y = one;
        let q_sub_a = d.sub(q, a);
        let z = d.mul(a, q_sub_a);
        let z_upper_ty = d.le(z, capital_n);
        let z_upper_fv = d.fresh_fvar();
        let z_upper = d.k.fvar(z_upper_fv);

        let one_le_two = d.lemma(p.le_add_right, &[one, one]);
        let ha = d.lemma(p.le_trans, &[one, two, a, one_le_two, ha_two]);

        // Y is a unit in the left interval [1,ab].
        let a_times_one = d.mul(a, one);
        let a_times_one_le_ab = d.lemma(p.mul_le_mul_left, &[a, one, b, hb]);
        let a_times_one_eq_a = d.lemma(p.mul_one, &[a]);
        let a_le_ab =
            transport_le_lower(d, a_times_one, a, ab, a_times_one_le_ab, a_times_one_eq_a);
        let one_le_ab = d.lemma(p.le_trans, &[one, a, ab, ha, a_le_ab]);
        let one_le_one = d.lemma(p.le_refl, &[one]);
        let y_left_interval_ty = d.in_closed_interval(one, ab, y);
        let one_le_y_ty = d.le(one, y);
        let y_le_ab_ty = d.le(y, ab);
        let y_left_interval = d.const_app(
            p.logic.and_intro,
            &[one_le_y_ty, y_le_ab_ty, one_le_one, one_le_ab],
        );
        let y_right_interval = d.in_closed_interval(x, capital_n, y);
        let y_shell = d.const_app(
            p.logic.or_inl,
            &[y_left_interval_ty, y_right_interval, y_left_interval],
        );
        let y_shell_ty = shell_two_member(d, defs, capital_n, ab, y);
        let y_not_dvd = d.lemma(p.not_dvd_one_of_two_le, &[a, ha_two]);
        let y_not_dvd_ty = {
            let divides = d.dvd(a, y);
            d.const_app(p.logic.not, &[divides])
        };
        let y_unit_shell_ty = d.const_app(p.logic.and, &[y_not_dvd_ty, y_shell_ty]);
        let y_unit_shell = d.const_app(
            p.logic.and_intro,
            &[y_not_dvd_ty, y_shell_ty, y_not_dvd, y_shell],
        );
        let y_valuation_ty = d.valuation_at(a, y, two);
        let y_classified = d.const_app(
            p.logic.or_inr,
            &[y_valuation_ty, y_unit_shell_ty, y_unit_shell],
        );
        let y_lower = one_le_one;
        let y_upper = d.lemma(ranges.y_upper, &[a, b, n, ha, hb]);
        let y_domain_ty = d.in_closed_interval(one, capital_n, y);
        let y_le_n_ty = d.le(y, capital_n);
        let y_domain = d.const_app(
            p.logic.and_intro,
            &[one_le_y_ty, y_le_n_ty, y_lower, y_upper],
        );
        let y_classified_ty = d.const_app(p.logic.or, &[y_valuation_ty, y_unit_shell_ty]);
        let y_colour = d.const_app(
            p.logic.and_intro,
            &[y_domain_ty, y_classified_ty, y_domain, y_classified],
        );

        // X is the right shell endpoint and is congruent to one modulo a.
        let x_lower = d.lemma(ranges.x_lower, &[a, b, n]);
        let x_upper = d.lemma(ranges.x_upper, &[a, b, n, ha, hb]);
        let x_domain_ty = d.in_closed_interval(one, capital_n, x);
        let one_le_x_ty = d.le(one, x);
        let x_le_n_ty = d.le(x, capital_n);
        let x_domain = d.const_app(
            p.logic.and_intro,
            &[one_le_x_ty, x_le_n_ty, x_lower, x_upper],
        );
        let x_right_interval_ty = d.in_closed_interval(x, capital_n, x);
        let x_le_x_ty = d.le(x, x);
        let x_le_x = d.lemma(p.le_refl, &[x]);
        let x_right_interval =
            d.const_app(p.logic.and_intro, &[x_le_x_ty, x_le_n_ty, x_le_x, x_upper]);
        let x_left_interval = d.in_closed_interval(one, ab, x);
        let x_shell = d.const_app(
            p.logic.or_inr,
            &[x_left_interval, x_right_interval_ty, x_right_interval],
        );
        let x_shell_ty = shell_two_member(d, defs, capital_n, ab, x);

        let ba = d.mul(b, a);
        let capital_n_sub_ba = d.sub(capital_n, ba);
        let ab_eq_ba = d.lemma(p.mul_comm, &[a, b]);
        let difference_eq_n_sub_ba = d.congr(ab, ba, ab_eq_ba, &|d, t| d.sub(capital_n, t));
        let b_q_sub_a = d.mul(b, q_sub_a);
        let a_le_q = d.lemma(p.le_add_right, &[a, u]);
        let n_sub_ba_eq_b_q_sub_a = {
            let distributed = d.lemma(p.mul_sub_left_distrib, &[b, q, a, a_le_q]);
            d.symm(b_q_sub_a, capital_n_sub_ba, distributed)
        };
        let restored = d.add(q_sub_a, a);
        let restored_eq_q = d.lemma(p.sub_add_cancel, &[a, q, a_le_q]);
        let u_plus_a = d.add(u, a);
        let q_eq_u_plus_a = d.lemma(p.add_comm, &[a, u]);
        let (_, common_sum) = d.chain(restored, &[(q, restored_eq_q), (u_plus_a, q_eq_u_plus_a)]);
        let q_sub_a_eq_u = d.lemma(p.add_right_cancel, &[q_sub_a, u, a, common_sum]);
        let b_u = d.mul(b, u);
        let b_q_sub_a_eq_b_u = d.congr(q_sub_a, u, q_sub_a_eq_u, &|d, t| d.mul(b, t));
        let ba_inner = d.mul(ba, inner);
        let b_assoc = d.lemma(p.mul_assoc, &[b, a, inner]);
        let b_u_eq_ba_inner = d.symm(ba_inner, b_u, b_assoc);
        let ab_inner = d.mul(ab, inner);
        let ba_eq_ab = d.lemma(p.mul_comm, &[b, a]);
        let ba_inner_eq_ab_inner = d.congr(ba, ab, ba_eq_ab, &|d, t| d.mul(t, inner));
        let b_inner = d.mul(b, inner);
        let a_b_inner = d.mul(a, b_inner);
        let ab_inner_eq_a_b_inner = d.lemma(p.mul_assoc, &[a, b, inner]);
        let (_, difference_eq_a_b_inner) = d.chain(
            difference,
            &[
                (capital_n_sub_ba, difference_eq_n_sub_ba),
                (b_q_sub_a, n_sub_ba_eq_b_q_sub_a),
                (b_u, b_q_sub_a_eq_b_u),
                (ba_inner, b_u_eq_ba_inner),
                (ab_inner, ba_inner_eq_ab_inner),
                (a_b_inner, ab_inner_eq_a_b_inner),
            ],
        );
        let one_plus_difference = d.add(one, difference);
        let x_eq_one_plus_difference = d.lemma(p.add_comm, &[difference, one]);
        let shaped_x = d.add(one, a_b_inner);
        let one_plus_difference_eq_shaped =
            d.congr(difference, a_b_inner, difference_eq_a_b_inner, &|d, t| {
                d.add(one, t)
            });
        let (_, x_eq_shaped) = d.chain(
            x,
            &[
                (one_plus_difference, x_eq_one_plus_difference),
                (shaped_x, one_plus_difference_eq_shaped),
            ],
        );
        let shaped_not_dvd = d.lemma(p.not_dvd_one_add_mul_of_two_le, &[a, b_inner, ha_two]);
        let shaped_eq_x = d.symm(x, shaped_x, x_eq_shaped);
        let x_not_dvd = {
            let motive = d.eq_motive(shaped_x, &|d, value| {
                let divides = d.dvd(a, value);
                d.const_app(p.logic.not, &[divides])
            });
            d.transport(shaped_x, motive, shaped_not_dvd, x, shaped_eq_x)
        };
        let x_not_dvd_ty = {
            let divides = d.dvd(a, x);
            d.const_app(p.logic.not, &[divides])
        };
        let x_unit_shell_ty = d.const_app(p.logic.and, &[x_not_dvd_ty, x_shell_ty]);
        let x_unit_shell = d.const_app(
            p.logic.and_intro,
            &[x_not_dvd_ty, x_shell_ty, x_not_dvd, x_shell],
        );
        let x_valuation_ty = d.valuation_at(a, x, two);
        let x_classified = d.const_app(
            p.logic.or_inr,
            &[x_valuation_ty, x_unit_shell_ty, x_unit_shell],
        );
        let x_classified_ty = d.const_app(p.logic.or, &[x_valuation_ty, x_unit_shell_ty]);
        let x_colour = d.const_app(
            p.logic.and_intro,
            &[x_domain_ty, x_classified_ty, x_domain, x_classified],
        );

        // Z is in the domain by the explicit guard and has exact valuation two.
        let z_lower = d.lemma(ranges.z_lower, &[a, b, n, ha]);
        let z_domain_ty = d.in_closed_interval(one, capital_n, z);
        let one_le_z_ty = d.le(one, z);
        let z_le_n_ty = d.le(z, capital_n);
        let z_domain = d.const_app(
            p.logic.and_intro,
            &[one_le_z_ty, z_le_n_ty, z_lower, z_upper],
        );
        let z_valuation_ty = d.valuation_at(a, z, two);
        let z_valuation = d.lemma(valuation, &[a, b, n, ha_two]);
        let z_not_dvd_ty = {
            let divides = d.dvd(a, z);
            d.const_app(p.logic.not, &[divides])
        };
        let z_shell_ty = shell_two_member(d, defs, capital_n, ab, z);
        let z_unit_shell_ty = d.const_app(p.logic.and, &[z_not_dvd_ty, z_shell_ty]);
        let z_classified = d.const_app(
            p.logic.or_inl,
            &[z_valuation_ty, z_unit_shell_ty, z_valuation],
        );
        let z_classified_ty = d.const_app(p.logic.or, &[z_valuation_ty, z_unit_shell_ty]);
        let z_colour = d.const_app(
            p.logic.and_intro,
            &[z_domain_ty, z_classified_ty, z_domain, z_classified],
        );

        let x_colour_ty = colour_two_at(d, defs, a, capital_n, ab, x);
        let y_colour_ty = colour_two_at(d, defs, a, capital_n, ab, y);
        let z_colour_ty = colour_two_at(d, defs, a, capital_n, ab, z);
        let yz_ty = d.const_app(p.logic.and, &[y_colour_ty, z_colour_ty]);
        let yz = d.const_app(
            p.logic.and_intro,
            &[y_colour_ty, z_colour_ty, y_colour, z_colour],
        );
        let body = d.const_app(p.logic.and_intro, &[x_colour_ty, yz_ty, x_colour, yz]);
        let conclusion = d.const_app(p.logic.and, &[x_colour_ty, yz_ty]);
        let proof = {
            let with_z_upper = d.lam_fv(z_upper_fv, z_upper_ty, body);
            let with_hb = d.lam_fv(hb_fv, hb_ty, with_z_upper);
            d.lam_fv(ha_two_fv, ha_two_ty, with_hb)
        };
        let stmt = {
            let with_z_upper = d.arrow(z_upper_ty, conclusion);
            let with_hb = d.arrow(hb_ty, with_z_upper);
            d.arrow(ha_two_ty, with_hb)
        };
        (stmt, proof)
    })
    .expect("closed-form witness colour-two theorem checks");
    name
}

/// Package the exact checked content of `thm:sharp` that the current library
/// can state without pretending a global colouring or Ramsey predicate exists.
fn admit_closed_form_sharp_certificate(
    d: &mut Dev,
    defs: ColourTwoDefinitions,
    witness_identity: NameId,
    ranges: RangeTheorems,
    exact_range: NameId,
    witness_colour_two: NameId,
) -> NameId {
    let p = d.p;
    let name = d.name("closed_form_sharp_certificate");
    d.theorem(name, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let two = d.num(2);
        let ha_two_ty = d.le(two, a);
        let ha_two_fv = d.fresh_fvar();
        let ha_two = d.k.fvar(ha_two_fv);
        let hb_ty = d.le(one, b);
        let hb_fv = d.fresh_fvar();
        let hb = d.k.fvar(hb_fv);

        let shifted = power_range(d, a, 1);
        let sum = d.sum_range(shifted, n);
        let sn = d.succ(n);
        let power = d.pow(a, sn);
        let twice_sum = d.mul(two, sum);
        let tail = d.add(twice_sum, power);
        let inner = d.add(one, tail);
        let u = d.mul(a, inner);
        let q = d.add(a, u);
        let capital_n = d.mul(b, q);
        let ab = d.mul(a, b);
        let difference = d.sub(capital_n, ab);
        let x = d.add(difference, one);
        let y = one;
        let x_sub_y = d.sub(x, y);
        let lhs = d.mul(a, x_sub_y);
        let q_sub_a = d.sub(q, a);
        let z = d.mul(a, q_sub_a);
        let rhs = d.mul(b, z);
        let identity_ty = d.eq(lhs, rhs);

        let one_le_two = d.lemma(p.le_add_right, &[one, one]);
        let ha = d.lemma(p.le_trans, &[one, two, a, one_le_two, ha_two]);
        let identity = d.lemma(witness_identity, &[a, b, n]);

        let x_domain_ty = d.in_closed_interval(one, capital_n, x);
        let x_lower = d.lemma(ranges.x_lower, &[a, b, n]);
        let x_upper = d.lemma(ranges.x_upper, &[a, b, n, ha, hb]);
        let one_le_x_ty = d.le(one, x);
        let x_le_n_ty = d.le(x, capital_n);
        let x_domain = d.const_app(
            p.logic.and_intro,
            &[one_le_x_ty, x_le_n_ty, x_lower, x_upper],
        );

        let y_domain_ty = d.in_closed_interval(one, capital_n, y);
        let one_le_y_ty = d.le(one, y);
        let y_le_n_ty = d.le(y, capital_n);
        let y_lower = d.lemma(p.le_refl, &[one]);
        let y_upper = d.lemma(ranges.y_upper, &[a, b, n, ha, hb]);
        let y_domain = d.const_app(
            p.logic.and_intro,
            &[one_le_y_ty, y_le_n_ty, y_lower, y_upper],
        );

        let z_range_ty = d.le(z, capital_n);
        let a_sub_b = d.sub(a, b);
        let criterion_lhs = d.mul(capital_n, a_sub_b);
        let aa = d.mul(a, a);
        let criterion_rhs = d.mul(aa, b);
        let criterion_ty = d.le(criterion_lhs, criterion_rhs);
        let exact_range_ty = d.const_app(p.logic.iff, &[z_range_ty, criterion_ty]);
        let exact_range_proof = d.lemma(exact_range, &[a, b, n, hb]);

        let x_colour_ty = colour_two_at(d, defs, a, capital_n, ab, x);
        let y_colour_ty = colour_two_at(d, defs, a, capital_n, ab, y);
        let z_colour_ty = colour_two_at(d, defs, a, capital_n, ab, z);
        let yz_colour_ty = d.const_app(p.logic.and, &[y_colour_ty, z_colour_ty]);
        let colours_ty = d.const_app(p.logic.and, &[x_colour_ty, yz_colour_ty]);
        let colour_when_in_range_ty = d.arrow(z_range_ty, colours_ty);
        let colour_when_in_range = d.lemma(witness_colour_two, &[a, b, n, ha_two, hb]);

        let range_and_colour_ty =
            d.const_app(p.logic.and, &[exact_range_ty, colour_when_in_range_ty]);
        let range_and_colour = d.const_app(
            p.logic.and_intro,
            &[
                exact_range_ty,
                colour_when_in_range_ty,
                exact_range_proof,
                colour_when_in_range,
            ],
        );
        let y_and_rest_ty = d.const_app(p.logic.and, &[y_domain_ty, range_and_colour_ty]);
        let y_and_rest = d.const_app(
            p.logic.and_intro,
            &[y_domain_ty, range_and_colour_ty, y_domain, range_and_colour],
        );
        let x_and_rest_ty = d.const_app(p.logic.and, &[x_domain_ty, y_and_rest_ty]);
        let x_and_rest = d.const_app(
            p.logic.and_intro,
            &[x_domain_ty, y_and_rest_ty, x_domain, y_and_rest],
        );
        let conclusion = d.const_app(p.logic.and, &[identity_ty, x_and_rest_ty]);
        let body = d.const_app(
            p.logic.and_intro,
            &[identity_ty, x_and_rest_ty, identity, x_and_rest],
        );
        let proof = {
            let with_hb = d.lam_fv(hb_fv, hb_ty, body);
            d.lam_fv(ha_two_fv, ha_two_ty, with_hb)
        };
        let stmt = {
            let with_hb = d.arrow(hb_ty, conclusion);
            d.arrow(ha_two_ty, with_hb)
        };
        (stmt, proof)
    })
    .expect("closed-form sharpness certificate checks");
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
fn kernel_checks_the_closed_form_witness_valuation() {
    let mut d = Dev::new();
    let theorem = admit_closed_form_witness_valuation(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let bound = d.lemma(d.p.le_refl, &[a]);
    let proof = d.lemma(theorem, &[a, b, zero, bound]);
    d.k.infer(proof)
        .expect("closed-form empty-corner valuation infers");

    let axioms: Vec<_> =
        d.k.environment()
            .iter()
            .filter(|(_, decl)| matches!(decl, Declaration::Axiom { .. }))
            .collect();
    assert!(
        axioms.is_empty(),
        "closed-form valuation must add no axioms"
    );
}

#[test]
fn kernel_rejects_a_broken_closed_form_witness_valuation() {
    let mut d = Dev::new();
    let theorem = admit_closed_form_witness_valuation(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let bound = d.lemma(d.p.le_refl, &[a]);
    let proof = d.lemma(theorem, &[a, b, zero, bound]);

    // At n=0 the closed form has Z=12 and exact base-two valuation 2.
    // Changing only the valuation exponent must not inherit that proof.
    let twelve = d.num(12);
    let one = d.num(1);
    let bad = d.valuation_at(a, twelve, one);
    let bad_name = d.name("broken_closed_form_witness_valuation");
    let error =
        d.k.add_declaration(Declaration::Theorem {
            name: bad_name,
            uparams: vec![],
            ty: bad,
            value: proof,
        })
        .expect_err("a changed valuation exponent must be rejected");
    println!("broken closed-form witness valuation rejected: {error:?}");
    assert!(!d.k.environment().contains(bad_name));
}

#[test]
fn kernel_checks_the_closed_form_witness_colour_two() {
    let mut d = Dev::new();
    let defs = define_colour_two_relations(&mut d);
    let ranges = admit_closed_form_range_theorems(&mut d);
    let valuation = admit_closed_form_witness_valuation(&mut d);
    let theorem = admit_closed_form_witness_colour_two(&mut d, defs, ranges, valuation);

    // Empty-range corner: a=2, b=3, n=0 gives N=24, X=19, Y=1, Z=12.
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);
    let ha = d.lemma(d.p.le_refl, &[a]);
    let hb = d.lemma(d.p.le_add_right, &[one, two]);
    let twelve = d.num(12);
    let twelve_more = d.num(12);
    let z_upper = d.lemma(d.p.le_add_right, &[twelve, twelve_more]);
    let proof = d.lemma(theorem, &[a, b, zero, ha, hb, z_upper]);
    d.k.infer(proof)
        .expect("closed-form colour-two application infers");

    let axioms: Vec<_> =
        d.k.environment()
            .iter()
            .filter(|(_, decl)| matches!(decl, Declaration::Axiom { .. }))
            .collect();
    assert!(axioms.is_empty(), "colour-two theorem must add no axioms");
}

#[test]
fn kernel_rejects_a_broken_closed_form_witness_colour_two_shell() {
    let mut d = Dev::new();
    let defs = define_colour_two_relations(&mut d);
    let ranges = admit_closed_form_range_theorems(&mut d);
    let valuation = admit_closed_form_witness_valuation(&mut d);
    let theorem = admit_closed_form_witness_colour_two(&mut d, defs, ranges, valuation);
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);
    let ha = d.lemma(d.p.le_refl, &[a]);
    let hb = d.lemma(d.p.le_add_right, &[one, two]);
    let twelve = d.num(12);
    let twelve_more = d.num(12);
    let z_upper = d.lemma(d.p.le_add_right, &[twelve, twelve_more]);
    let proof = d.lemma(theorem, &[a, b, zero, ha, hb, z_upper]);

    // The checked shell has ab=6 and right endpoint 19. Changing only the
    // shell width to five moves its right interval to [20,24].
    let capital_n = d.num(24);
    let broken_ab = d.num(5);
    let x = d.num(19);
    let y = one;
    let z = twelve;
    let x_colour = colour_two_at(&mut d, defs, a, capital_n, broken_ab, x);
    let y_colour = colour_two_at(&mut d, defs, a, capital_n, broken_ab, y);
    let z_colour = colour_two_at(&mut d, defs, a, capital_n, broken_ab, z);
    let yz = d.const_app(d.p.logic.and, &[y_colour, z_colour]);
    let bad = d.const_app(d.p.logic.and, &[x_colour, yz]);
    let bad_name = d.name("broken_closed_form_witness_colour_two_shell");
    let error =
        d.k.add_declaration(Declaration::Theorem {
            name: bad_name,
            uparams: vec![],
            ty: bad,
            value: proof,
        })
        .expect_err("a changed shell width must be rejected");
    println!("broken closed-form colour-two shell rejected: {error:?}");
    assert!(!d.k.environment().contains(bad_name));
}

fn build_closed_form_sharp_certificate(d: &mut Dev) -> NameId {
    let defs = define_colour_two_relations(d);
    let witness = admit_sharp_witness_identity(d);
    let closed_witness = admit_closed_form_sharp_witness_identity(d, witness);
    let ranges = admit_closed_form_range_theorems(d);
    let exact = admit_exact_range_criterion(d);
    let closed_exact = admit_closed_form_exact_range_criterion(d, exact);
    let valuation = admit_closed_form_witness_valuation(d);
    let colours = admit_closed_form_witness_colour_two(d, defs, ranges, valuation);
    admit_closed_form_sharp_certificate(d, defs, closed_witness, ranges, closed_exact, colours)
}

#[test]
fn kernel_checks_the_closed_form_sharp_certificate() {
    let mut d = Dev::new();
    let certificate = build_closed_form_sharp_certificate(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);
    let ha = d.lemma(d.p.le_refl, &[a]);
    let hb = d.lemma(d.p.le_add_right, &[one, two]);
    let proof = d.lemma(certificate, &[a, b, zero, ha, hb]);
    d.k.infer(proof)
        .expect("closed-form sharpness certificate application infers");

    let axioms: Vec<_> =
        d.k.environment()
            .iter()
            .filter(|(_, decl)| matches!(decl, Declaration::Axiom { .. }))
            .collect();
    assert!(
        axioms.is_empty(),
        "sharpness certificate must add no axioms"
    );
}

#[test]
fn kernel_rejects_a_sharp_certificate_with_the_wrong_b_bound() {
    let mut d = Dev::new();
    let certificate = build_closed_form_sharp_certificate(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let ha = d.lemma(d.p.le_refl, &[a]);

    // The final premise is 1<=b. Reusing the unrelated 2<=a proof must fail
    // before any purported certificate can be checked.
    let broken = d.lemma(certificate, &[a, b, zero, ha, ha]);
    let error =
        d.k.infer(broken)
            .expect_err("the certificate must retain the positive-b premise");
    println!("wrong sharpness-certificate b bound rejected: {error:?}");
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

#[test]
fn kernel_checks_the_closed_form_witness_ranges() {
    let mut d = Dev::new();
    let ranges = admit_closed_form_range_theorems(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);
    let ha = d.lemma(d.p.le_add_right, &[one, one]);
    let hb = d.lemma(d.p.le_add_right, &[one, two]);
    let hab = d.lemma(d.p.le_add_right, &[a, one]);

    for proof in [
        d.lemma(ranges.x_lower, &[a, b, zero]),
        d.lemma(ranges.y_upper, &[a, b, zero, ha, hb]),
        d.lemma(ranges.x_upper, &[a, b, zero, ha, hb]),
        d.lemma(ranges.z_lower, &[a, b, zero, ha]),
        d.lemma(ranges.z_upper_if_a_le_b, &[a, b, zero, hab]),
    ] {
        d.k.infer(proof).expect("closed-form range proof infers");
    }

    // Concrete anti-vacuity: X=19 and Z=12 both lie in [1,24]. The upper
    // bound for Z is supplied explicitly, matching the paper theorem's guard.
    let nineteen = d.num(19);
    let twenty_four = d.num(24);
    let twelve = d.num(12);
    let five = d.num(5);
    let twelve_more = d.num(12);
    let x_upper = d.lemma(d.p.le_add_right, &[nineteen, five]);
    let z_upper = d.lemma(d.p.le_add_right, &[twelve, twelve_more]);
    let inferred_x_upper = d.k.infer(x_upper).expect("X upper infers");
    let expected_x_upper = d.le(nineteen, twenty_four);
    assert!(d.k.def_eq(inferred_x_upper, expected_x_upper));
    let inferred_z_upper = d.k.infer(z_upper).expect("Z upper infers");
    let expected_z_upper = d.le(twelve, twenty_four);
    assert!(d.k.def_eq(inferred_z_upper, expected_z_upper));
}

#[test]
fn kernel_checks_the_exact_rado_range_criterion() {
    let mut d = Dev::new();
    let theorem = admit_exact_range_criterion(&mut d);
    let closed = admit_closed_form_exact_range_criterion(&mut d, theorem);

    // a<=b branch: a=2, b=3, q=8, N=24, Z=12.
    let a = d.num(2);
    let b = d.num(3);
    let q = d.num(8);
    let capital_n = d.num(24);
    let factor = d.refl(capital_n);
    let six = d.num(6);
    let a_le_q = d.lemma(d.p.le_add_right, &[a, six]);
    let one = d.num(1);
    let two = d.num(2);
    let positive = d.lemma(d.p.le_add_right, &[one, two]);
    let easy = d.lemma(theorem, &[a, b, capital_n, q, factor, a_le_q, positive]);
    d.k.infer(easy)
        .expect("a<=b exact-range application infers");
    let zero = d.zero();
    let closed_easy = d.lemma(closed, &[a, b, zero, positive]);
    d.k.infer(closed_easy)
        .expect("closed-form a<=b exact-range application infers");

    // b<=a branch: a=3, b=2, q=5, N=10, Z=6 and 10*(3-2)<=18.
    let a = d.num(3);
    let b = d.num(2);
    let q = d.num(5);
    let capital_n = d.num(10);
    let factor = d.refl(capital_n);
    let two = d.num(2);
    let a_le_q = d.lemma(d.p.le_add_right, &[a, two]);
    let one = d.num(1);
    let positive = d.lemma(d.p.le_add_right, &[one, one]);
    let signed = d.lemma(theorem, &[a, b, capital_n, q, factor, a_le_q, positive]);
    d.k.infer(signed)
        .expect("b<=a exact-range application infers");
    let zero = d.zero();
    let closed_signed = d.lemma(closed, &[a, b, zero, positive]);
    d.k.infer(closed_signed)
        .expect("closed-form b<=a exact-range application infers");

    let axioms: Vec<_> =
        d.k.environment()
            .iter()
            .filter(|(_, decl)| matches!(decl, Declaration::Axiom { .. }))
            .collect();
    assert!(
        axioms.is_empty(),
        "exact range criterion must add no axioms"
    );
}

#[test]
fn kernel_rejects_a_broken_exact_rado_range_criterion() {
    let mut d = Dev::new();
    let theorem = admit_exact_range_criterion(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let q = d.num(8);
    let capital_n = d.num(24);
    let factor = d.refl(capital_n);
    let six = d.num(6);
    let a_le_q = d.lemma(d.p.le_add_right, &[a, six]);
    let one = d.num(1);
    let two = d.num(2);
    let positive = d.lemma(d.p.le_add_right, &[one, two]);
    let proof = d.lemma(theorem, &[a, b, capital_n, q, factor, a_le_q, positive]);

    let u = d.sub(q, a);
    let z = d.mul(a, u);
    let range = d.le(z, capital_n);
    let a_sub_b = d.sub(a, b);
    let lhs = d.mul(capital_n, a_sub_b);
    let eleven = d.num(11);
    let broken_criterion = d.le(lhs, eleven);
    let false_goal = d.const_app(d.p.logic.iff, &[range, broken_criterion]);
    let bad_name = d.name("broken_exact_range_criterion");
    let error =
        d.k.add_declaration(Declaration::Theorem {
            name: bad_name,
            uparams: vec![],
            ty: false_goal,
            value: proof,
        })
        .expect_err("a changed a^2*b endpoint must be rejected");
    println!("broken exact Rado range criterion rejected: {error:?}");
    assert!(!d.k.environment().contains(bad_name));
}

#[test]
fn kernel_rejects_a_broken_closed_form_x_upper_bound() {
    let mut d = Dev::new();
    let ranges = admit_closed_form_range_theorems(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);
    let ha = d.lemma(d.p.le_add_right, &[one, one]);
    let hb = d.lemma(d.p.le_add_right, &[one, two]);
    let proof = d.lemma(ranges.x_upper, &[a, b, zero, ha, hb]);

    // The checked target is X=19 <= N=24. Replacing N by 18 is false and
    // must not inherit the valid range proof.
    let nineteen = d.num(19);
    let eighteen = d.num(18);
    let false_goal = d.le(nineteen, eighteen);
    let bad_name = d.name("broken_closed_form_x_upper");
    let error =
        d.k.add_declaration(Declaration::Theorem {
            name: bad_name,
            uparams: vec![],
            ty: false_goal,
            value: proof,
        })
        .expect_err("a false closed-form X upper bound must be rejected");
    println!("broken closed-form X upper bound rejected: {error:?}");
    assert!(!d.k.environment().contains(bad_name));
}

#[test]
fn kernel_rejects_a_broken_closed_form_z_upper_bound() {
    let mut d = Dev::new();
    let ranges = admit_closed_form_range_theorems(&mut d);
    let a = d.num(2);
    let b = d.num(3);
    let zero = d.zero();
    let one = d.num(1);
    let hab = d.lemma(d.p.le_add_right, &[a, one]);
    let proof = d.lemma(ranges.z_upper_if_a_le_b, &[a, b, zero, hab]);

    // The checked target is Z=12 <= N=24. Replacing N by 11 is false and
    // must not inherit the sufficient-branch range proof.
    let twelve = d.num(12);
    let eleven = d.num(11);
    let false_goal = d.le(twelve, eleven);
    let bad_name = d.name("broken_closed_form_z_upper");
    let error =
        d.k.add_declaration(Declaration::Theorem {
            name: bad_name,
            uparams: vec![],
            ty: false_goal,
            value: proof,
        })
        .expect_err("a false closed-form Z upper bound must be rejected");
    println!("broken closed-form Z upper bound rejected: {error:?}");
    assert!(!d.k.environment().contains(bad_name));
}
