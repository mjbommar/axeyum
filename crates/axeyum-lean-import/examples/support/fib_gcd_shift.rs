//! Fixed support constructors for the Fibonacci gcd-shift operation.

use axeyum_lean_import::{canonical_declaration_sha256, canonical_expression_sha256};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, NameId, NatOps, NatPrelude, NatState,
};
use serde_json::{Value, json};

pub(crate) const ADDITION_TARGET: &str = "Axeyum.Autogenesis.NatFibSuccessorAddition";
pub(crate) const CANCELLATION_TARGET: &str =
    "Axeyum.Autogenesis.NatCoprimeFactorDivisibilityCancellation";

const CANCELLATION_DEPENDENCIES: &[&str] = &[
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.dvd_add",
    "Nat.dvd_add_iff_right",
    "Nat.dvd_mul_right_of_dvd",
    "Nat.gcd_bezout",
    "Nat.mul_assoc",
    "Nat.mul_comm",
    "Nat.one_mul",
    "Nat.right_distrib",
];

pub(crate) struct CheckedSupport {
    pub(crate) kernel: Kernel,
    pub(crate) evidence: Value,
}

struct Admission {
    kernel: Kernel,
    goal_sha256: String,
    proof_sha256: String,
    declaration_sha256: String,
    axiom_footprint: Vec<String>,
    direct_theorem_dependencies: Vec<String>,
}

struct FibDev<'k> {
    kernel: &'k mut Kernel,
    state: NatState,
    fib: NameId,
    recurrence: NameId,
}

impl<'k> FibDev<'k> {
    fn new(
        kernel: &'k mut Kernel,
        prelude: &NatPrelude,
        recurrence_name: &str,
    ) -> Result<Self, String> {
        let fib = exact_name(kernel, "Nat.fib")?;
        let recurrence = exact_name(kernel, recurrence_name)?;
        let state = NatState::new(kernel, *prelude);
        Ok(Self {
            kernel,
            state,
            fib,
            recurrence,
        })
    }

    fn fib(&mut self, n: ExprId) -> ExprId {
        let fib = self.kernel.const_(self.fib, vec![]);
        self.kernel.app(fib, n)
    }

    fn formula(&mut self, n: ExprId, k: ExprId) -> ExprId {
        let succ_k = self.succ(k);
        let succ_n = self.succ(n);
        let shifted = self.add(n, succ_k);
        let left = self.fib(shifted);
        let fib_succ_k = self.fib(succ_k);
        let fib_succ_n = self.fib(succ_n);
        let first = self.mul(fib_succ_k, fib_succ_n);
        let fib_k = self.fib(k);
        let fib_n = self.fib(n);
        let second = self.mul(fib_k, fib_n);
        let right = self.add(first, second);
        self.eq(left, right)
    }

    fn sides(&mut self, n: ExprId, k: ExprId) -> (ExprId, ExprId) {
        let succ_k = self.succ(k);
        let succ_n = self.succ(n);
        let shifted = self.add(n, succ_k);
        let left = self.fib(shifted);
        let fib_succ_k = self.fib(succ_k);
        let fib_succ_n = self.fib(succ_n);
        let first = self.mul(fib_succ_k, fib_succ_n);
        let fib_k = self.fib(k);
        let fib_n = self.fib(n);
        let second = self.mul(fib_k, fib_n);
        let right = self.add(first, second);
        (left, right)
    }

    fn and(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let name = self.prelude().logic.and;
        self.const_app(name, &[left, right])
    }

    fn and_intro(
        &mut self,
        left: ExprId,
        right: ExprId,
        left_proof: ExprId,
        right_proof: ExprId,
    ) -> ExprId {
        let name = self.prelude().logic.and_intro;
        self.const_app(name, &[left, right, left_proof, right_proof])
    }

    fn and_left(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let logic = self.prelude().logic;
        let pair = self.and(left, right);
        let motive = {
            let pair_fv = self.fresh_fvar();
            self.lam_fv(pair_fv, pair, left)
        };
        let minor = {
            let left_fv = self.fresh_fvar();
            let left_value = self.kernel.fvar(left_fv);
            let right_fv = self.fresh_fvar();
            let with_right = self.lam_fv(right_fv, right, left_value);
            self.lam_fv(left_fv, left, with_right)
        };
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(logic.and_rec, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }

    fn and_right(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let logic = self.prelude().logic;
        let pair = self.and(left, right);
        let motive = {
            let pair_fv = self.fresh_fvar();
            self.lam_fv(pair_fv, pair, right)
        };
        let minor = {
            let left_fv = self.fresh_fvar();
            let right_fv = self.fresh_fvar();
            let right_value = self.kernel.fvar(right_fv);
            let with_right = self.lam_fv(right_fv, right, right_value);
            self.lam_fv(left_fv, left, with_right)
        };
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(logic.and_rec, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }

    fn recurrence(&mut self, n: ExprId) -> ExprId {
        self.lemma(self.recurrence, &[n])
    }

    fn congr_fib(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        self.congr(left, right, proof, &|d, value| d.fib(value))
    }

    fn congr_succ(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        self.congr(left, right, proof, &|d, value| d.succ(value))
    }

    fn congr_add_left(
        &mut self,
        fixed: ExprId,
        left: ExprId,
        right: ExprId,
        proof: ExprId,
    ) -> ExprId {
        self.congr(left, right, proof, &|d, value| d.add(fixed, value))
    }

    fn congr_add_right(
        &mut self,
        left: ExprId,
        right: ExprId,
        fixed: ExprId,
        proof: ExprId,
    ) -> ExprId {
        self.congr(left, right, proof, &|d, value| d.add(value, fixed))
    }

    fn congr_mul_left(
        &mut self,
        fixed: ExprId,
        left: ExprId,
        right: ExprId,
        proof: ExprId,
    ) -> ExprId {
        self.congr(left, right, proof, &|d, value| d.mul(fixed, value))
    }

    fn base_zero(&mut self, k: ExprId) -> ExprId {
        let p = self.prelude();
        let zero = self.zero();
        let one = self.succ(zero);
        let succ_k = self.succ(k);
        let fib_succ_k = self.fib(succ_k);
        let fib_k = self.fib(k);
        let fib_zero = self.fib(zero);
        let fib_one = self.fib(one);
        let (left, right) = self.sides(zero, k);

        let shifted = self.add(zero, succ_k);
        let zero_add = self.lemma(p.zero_add, &[succ_k]);
        let left_to_center = self.congr_fib(shifted, succ_k, zero_add);

        let first = self.mul(fib_succ_k, fib_one);
        let second = self.mul(fib_k, fib_zero);
        let first_to = self.lemma(p.mul_one, &[fib_succ_k]);
        let right_mid = self.add(fib_succ_k, second);
        let first_context = self.congr_add_right(first, fib_succ_k, second, first_to);
        let second_to = self.lemma(p.mul_zero, &[fib_k]);
        let right_zero = self.add(fib_succ_k, zero);
        let second_context = self.congr_add_left(fib_succ_k, second, zero, second_to);
        let right_to_zero = self.trans(right, right_mid, right_zero, first_context, second_context);
        let add_zero = self.lemma(p.add_zero, &[fib_succ_k]);
        let right_to_center = self.trans(right, right_zero, fib_succ_k, right_to_zero, add_zero);
        let center_to_right = self.symm(right, fib_succ_k, right_to_center);
        self.trans(left, fib_succ_k, right, left_to_center, center_to_right)
    }

    fn base_one(&mut self, k: ExprId) -> ExprId {
        let p = self.prelude();
        let zero = self.zero();
        let one = self.succ(zero);
        let two = self.succ(one);
        let succ_k = self.succ(k);
        let succ_succ_k = self.succ(succ_k);
        let fib_k = self.fib(k);
        let fib_succ_k = self.fib(succ_k);
        let fib_one = self.fib(one);
        let fib_two = self.fib(two);
        let (left, right) = self.sides(one, k);

        let one_plus = self.add(one, succ_k);
        let zero_plus = self.add(zero, succ_k);
        let succ_zero_plus = self.succ(zero_plus);
        let succ_add = self.lemma(p.succ_add, &[zero, succ_k]);
        let zero_add = self.lemma(p.zero_add, &[succ_k]);
        let lifted = self.congr_succ(zero_plus, succ_k, zero_add);
        let index = self.trans(one_plus, succ_zero_plus, succ_succ_k, succ_add, lifted);
        let left_to_fib = self.congr_fib(one_plus, succ_succ_k, index);
        let recurrence = self.recurrence(k);
        let sum_k_succ = self.add(fib_k, fib_succ_k);
        let sum_succ_k = self.add(fib_succ_k, fib_k);
        let commute = self.lemma(p.add_comm, &[fib_k, fib_succ_k]);
        let fib_succ_succ_k = self.fib(succ_succ_k);
        let fib_to_sum = self.trans(fib_succ_succ_k, sum_k_succ, sum_succ_k, recurrence, commute);
        let left_to_sum = self.trans(left, fib_succ_succ_k, sum_succ_k, left_to_fib, fib_to_sum);

        let first = self.mul(fib_succ_k, fib_two);
        let second = self.mul(fib_k, fib_one);
        let first_to = self.lemma(p.mul_one, &[fib_succ_k]);
        let right_mid = self.add(fib_succ_k, second);
        let first_context = self.congr_add_right(first, fib_succ_k, second, first_to);
        let second_to = self.lemma(p.mul_one, &[fib_k]);
        let second_context = self.congr_add_left(fib_succ_k, second, fib_k, second_to);
        let right_to_sum = self.trans(right, right_mid, sum_succ_k, first_context, second_context);
        let sum_to_right = self.symm(right, sum_succ_k, right_to_sum);
        self.trans(left, sum_succ_k, right, left_to_sum, sum_to_right)
    }

    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn step_second(&mut self, n: ExprId, k: ExprId, ih_n: ExprId, ih_succ: ExprId) -> ExprId {
        let p = self.prelude();
        let zero = self.zero();
        let one = self.succ(zero);
        let two = self.succ(one);
        let succ_n = self.succ(n);
        let succ_succ_n = self.succ(succ_n);
        let succ_succ_succ_n = self.succ(succ_succ_n);
        let succ_k = self.succ(k);
        let (left_n, right_n) = self.sides(n, k);
        let (left_succ, right_succ) = self.sides(succ_n, k);
        let (left_two, right_two) = self.sides(succ_succ_n, k);

        let base_index = self.add(n, succ_k);
        let succ_index = self.add(succ_n, succ_k);
        let two_index = self.add(succ_succ_n, succ_k);
        let succ_base = self.succ(base_index);
        let succ_succ_base = self.succ(succ_base);
        let succ_add_n = self.lemma(p.succ_add, &[n, succ_k]);
        let succ_add_succ = self.lemma(p.succ_add, &[succ_n, succ_k]);
        let lifted_succ_add = self.congr_succ(succ_index, succ_base, succ_add_n);
        let succ_succ_index = self.succ(succ_index);
        let two_to_succ_succ = self.trans(
            two_index,
            succ_succ_index,
            succ_succ_base,
            succ_add_succ,
            lifted_succ_add,
        );
        let add_two_index = self.add(base_index, two);
        let defeq_two = self.refl(succ_succ_base);
        let two_index_to_recurrence = self.trans(
            two_index,
            succ_succ_base,
            add_two_index,
            two_to_succ_succ,
            defeq_two,
        );
        let left_to_recurrence = self.congr_fib(two_index, add_two_index, two_index_to_recurrence);
        let recurrence_at_index = self.recurrence(base_index);
        let add_one_index = self.add(base_index, one);
        let fib_base_index = self.fib(base_index);
        let fib_add_one_index = self.fib(add_one_index);
        let recurrence_sum = self.add(fib_base_index, fib_add_one_index);
        let fib_add_two_index = self.fib(add_two_index);
        let left_to_sum0 = self.trans(
            left_two,
            fib_add_two_index,
            recurrence_sum,
            left_to_recurrence,
            recurrence_at_index,
        );
        let succ_to_add_one = self.refl(succ_base);
        let succ_index_to_add_one = self.trans(
            succ_index,
            succ_base,
            add_one_index,
            succ_add_n,
            succ_to_add_one,
        );
        let add_one_to_succ_index = self.symm(succ_index, add_one_index, succ_index_to_add_one);
        let fib_add_one_to_succ = self.congr_fib(add_one_index, succ_index, add_one_to_succ_index);
        let sum_to_lefts = self.congr_add_left(
            fib_base_index,
            fib_add_one_index,
            left_succ,
            fib_add_one_to_succ,
        );
        let left_sum = self.add(left_n, left_succ);
        let left_to_sum = self.trans(
            left_two,
            recurrence_sum,
            left_sum,
            left_to_sum0,
            sum_to_lefts,
        );

        let fib_n = self.fib(n);
        let fib_succ_n = self.fib(succ_n);
        let fib_two_n = self.fib(succ_succ_n);
        let fib_three_n = self.fib(succ_succ_succ_n);
        let c = self.fib(succ_k);
        let d = self.fib(k);
        let c_three = self.mul(c, fib_three_n);
        let d_two = self.mul(d, fib_two_n);
        let yz = self.add(fib_succ_n, fib_two_n);
        let xy = self.add(fib_n, fib_succ_n);
        let c_yz = self.mul(c, yz);
        let d_xy = self.mul(d, xy);
        let rec_succ = self.recurrence(succ_n);
        let c_recurrence = self.congr_mul_left(c, fib_three_n, yz, rec_succ);
        let first_context = self.congr_add_right(c_three, c_yz, d_two, c_recurrence);
        let right_c_yz_d_two = self.add(c_yz, d_two);
        let rec_n = self.recurrence(n);
        let d_recurrence = self.congr_mul_left(d, fib_two_n, xy, rec_n);
        let second_context = self.congr_add_left(c_yz, d_two, d_xy, d_recurrence);
        let right_c_yz_d_xy = self.add(c_yz, d_xy);
        let right_to_recurrences = self.trans(
            right_two,
            right_c_yz_d_two,
            right_c_yz_d_xy,
            first_context,
            second_context,
        );

        let a = self.mul(c, fib_succ_n);
        let c_term = self.mul(c, fib_two_n);
        let b = self.mul(d, fib_n);
        let d_term = self.mul(d, fib_succ_n);
        let a_c = self.add(a, c_term);
        let b_d = self.add(b, d_term);
        let expanded = self.add(a_c, b_d);
        let distribute_c = self.lemma(p.left_distrib, &[c, fib_succ_n, fib_two_n]);
        let c_distribution_context = self.congr_add_right(c_yz, a_c, d_xy, distribute_c);
        let a_c_plus_dxy = self.add(a_c, d_xy);
        let distribute_d = self.lemma(p.left_distrib, &[d, fib_n, fib_succ_n]);
        let d_distribution_context = self.congr_add_left(a_c, d_xy, b_d, distribute_d);
        let recurrence_to_expanded = self.trans(
            right_c_yz_d_xy,
            a_c_plus_dxy,
            expanded,
            c_distribution_context,
            d_distribution_context,
        );
        let right_to_expanded = self.trans(
            right_two,
            right_c_yz_d_xy,
            expanded,
            right_to_recurrences,
            recurrence_to_expanded,
        );

        let a_c_b = self.add(a_c, b);
        let a_c_b_d = self.add(a_c_b, d_term);
        let assoc_ac_bd = self.lemma(p.add_assoc, &[a_c, b, d_term]);
        let expanded_to_acbd = self.symm(a_c_b_d, expanded, assoc_ac_bd);
        let a_b = self.add(a, b);
        let a_b_c = self.add(a_b, c_term);
        let a_b_c_d = self.add(a_b_c, d_term);
        let swap = self.lemma(p.add_right_comm, &[a, c_term, b]);
        let swap_context = self.congr_add_right(a_c_b, a_b_c, d_term, swap);
        let c_d = self.add(c_term, d_term);
        let pair_sum = self.add(a_b, c_d);
        let final_assoc = self.lemma(p.add_assoc, &[a_b, c_term, d_term]);
        let acbd_to_pair = self.trans(a_c_b_d, a_b_c_d, pair_sum, swap_context, final_assoc);
        let expanded_to_pair =
            self.trans(expanded, a_c_b_d, pair_sum, expanded_to_acbd, acbd_to_pair);
        let right_to_pair = self.trans(
            right_two,
            expanded,
            pair_sum,
            right_to_expanded,
            expanded_to_pair,
        );

        let left_sum_mid = self.add(right_n, left_succ);
        let ih_n_context = self.congr_add_right(left_n, right_n, left_succ, ih_n);
        let right_sum = self.add(right_n, right_succ);
        let ih_succ_context = self.congr_add_left(right_n, left_succ, right_succ, ih_succ);
        let left_sum_to_right = self.trans(
            left_sum,
            left_sum_mid,
            right_sum,
            ih_n_context,
            ih_succ_context,
        );
        let pair_to_right = self.symm(right_two, pair_sum, right_to_pair);
        let left_sum_to_target = self.trans(
            left_sum,
            right_sum,
            right_two,
            left_sum_to_right,
            pair_to_right,
        );
        self.trans(
            left_two,
            left_sum,
            right_two,
            left_to_sum,
            left_sum_to_target,
        )
    }

    fn paired_induction(&mut self, n: ExprId, k: ExprId) -> ExprId {
        let zero = self.zero();
        let succ_n = self.succ(n);
        let target_first = self.formula(n, k);
        let target_second = self.formula(succ_n, k);
        let induction = self.induct(
            &|d, j| {
                let succ_j = d.succ(j);
                let first = d.formula(j, k);
                let second = d.formula(succ_j, k);
                d.and(first, second)
            },
            &|d| {
                let one = d.succ(zero);
                let first = d.formula(zero, k);
                let second = d.formula(one, k);
                let first_proof = d.base_zero(k);
                let second_proof = d.base_one(k);
                d.and_intro(first, second, first_proof, second_proof)
            },
            &|d, j, ih| {
                let succ_j = d.succ(j);
                let succ_succ_j = d.succ(succ_j);
                let first = d.formula(j, k);
                let second = d.formula(succ_j, k);
                let ih_first = d.and_left(first, second, ih);
                let ih_second = d.and_right(first, second, ih);
                let next = d.formula(succ_succ_j, k);
                let next_proof = d.step_second(j, k, ih_first, ih_second);
                d.and_intro(second, next, ih_second, next_proof)
            },
            n,
        );
        self.and_left(target_first, target_second, induction)
    }
}

impl NatOps for FibDev<'_> {
    fn kernel(&mut self) -> &mut Kernel {
        self.kernel
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.state
    }
}

pub(crate) fn reconstruct_addition_twice(
    base: &Kernel,
    prelude: &NatPrelude,
    recurrence_name: &str,
) -> Result<CheckedSupport, String> {
    let first = admit_addition(base, prelude, recurrence_name)?;
    let replay = admit_addition(base, prelude, recurrence_name)?;
    if first.goal_sha256 != replay.goal_sha256
        || first.proof_sha256 != replay.proof_sha256
        || first.declaration_sha256 != replay.declaration_sha256
        || first.axiom_footprint != replay.axiom_footprint
        || first.direct_theorem_dependencies != replay.direct_theorem_dependencies
    {
        return Err("Fibonacci successor-addition reconstruction changed".to_owned());
    }
    if !first.axiom_footprint.is_empty() {
        return Err(format!(
            "Fibonacci successor-addition reaches assumptions: {:?}",
            first.axiom_footprint
        ));
    }
    let evidence = json!({
        "id": "fibonacci-successor-addition-v1",
        "target": ADDITION_TARGET,
        "goal_sha256": first.goal_sha256,
        "proof_sha256": first.proof_sha256,
        "declaration_sha256": first.declaration_sha256,
        "axiom_footprint": first.axiom_footprint,
        "direct_theorem_dependencies": first.direct_theorem_dependencies,
        "fresh_reconstructions": 2,
        "kernel_submissions": 2,
    });
    Ok(CheckedSupport {
        kernel: first.kernel,
        evidence,
    })
}

fn admit_addition(
    base: &Kernel,
    prelude: &NatPrelude,
    recurrence_name: &str,
) -> Result<Admission, String> {
    let mut kernel = base.clone();
    let target = nested_name(
        &mut kernel,
        &["Axeyum", "Autogenesis", "NatFibSuccessorAddition"],
    );
    {
        let mut d = FibDev::new(&mut kernel, prelude, recurrence_name)?;
        d.theorem(target, 2, &|d, values| {
            let n = values[0];
            let k = values[1];
            let statement = d.formula(n, k);
            let proof = d.paired_induction(n, k);
            (statement, proof)
        })
        .map_err(|error| {
            format!(
                "Fibonacci successor-addition rejected: {}",
                d.explain(&error)
            )
        })?;
    }
    let declaration = kernel
        .environment()
        .get(target)
        .ok_or("Fibonacci successor-addition disappeared")?;
    let Declaration::Theorem { ty, value, .. } = declaration else {
        return Err("Fibonacci successor-addition is not a theorem".to_owned());
    };
    let ty = *ty;
    let value = *value;
    Ok(Admission {
        goal_sha256: canonical_expression_sha256(&kernel, ty)?,
        proof_sha256: canonical_expression_sha256(&kernel, value)?,
        declaration_sha256: canonical_declaration_sha256(&kernel, target)?,
        axiom_footprint: rendered_names(&kernel, &kernel.axiom_footprint(target)),
        direct_theorem_dependencies: rendered_names(&kernel, &kernel.theorem_dependencies(target)),
        kernel,
    })
}

pub(crate) fn reconstruct_cancellation_twice(
    base: &Kernel,
    prelude: &NatPrelude,
) -> Result<CheckedSupport, String> {
    let first = admit_cancellation(base, prelude)?;
    let replay = admit_cancellation(base, prelude)?;
    if first.goal_sha256 != replay.goal_sha256
        || first.proof_sha256 != replay.proof_sha256
        || first.declaration_sha256 != replay.declaration_sha256
        || first.axiom_footprint != replay.axiom_footprint
        || first.direct_theorem_dependencies != replay.direct_theorem_dependencies
    {
        return Err("coprime-factor cancellation reconstruction changed".to_owned());
    }
    if !first.axiom_footprint.is_empty() {
        return Err(format!(
            "coprime-factor cancellation reaches assumptions: {:?}",
            first.axiom_footprint
        ));
    }
    let expected = CANCELLATION_DEPENDENCIES
        .iter()
        .map(|name| (*name).to_owned())
        .collect::<Vec<_>>();
    if first.direct_theorem_dependencies != expected {
        return Err(format!(
            "coprime-factor cancellation dependency set changed: {:?}",
            first.direct_theorem_dependencies
        ));
    }
    let evidence = json!({
        "id": "coprime-factor-divisibility-cancellation-v1",
        "target": CANCELLATION_TARGET,
        "goal_sha256": first.goal_sha256,
        "proof_sha256": first.proof_sha256,
        "declaration_sha256": first.declaration_sha256,
        "axiom_footprint": first.axiom_footprint,
        "direct_theorem_dependencies": first.direct_theorem_dependencies,
        "fresh_reconstructions": 2,
        "kernel_submissions": 2,
    });
    Ok(CheckedSupport {
        kernel: first.kernel,
        evidence,
    })
}

fn admit_cancellation(base: &Kernel, prelude: &NatPrelude) -> Result<Admission, String> {
    let mut kernel = base.clone();
    let target = nested_name(
        &mut kernel,
        &[
            "Axeyum",
            "Autogenesis",
            "NatCoprimeFactorDivisibilityCancellation",
        ],
    );
    {
        let mut d = FibDev::new(&mut kernel, prelude, "Axeyum.Autogenesis.fibAddTwo")?;
        d.theorem(target, 4, &|d, values| {
            let (a, c, b, divisor) = (values[0], values[1], values[2], values[3]);
            let one = d.num(1);
            let common = d.gcd(a, c);
            let coprime_ty = d.eq(common, one);
            let divides_a_ty = d.dvd(divisor, a);
            let product = d.mul(c, b);
            let divides_product_ty = d.dvd(divisor, product);
            let conclusion = d.dvd(divisor, b);
            let statement = {
                let with_product = d.arrow(divides_product_ty, conclusion);
                let with_a = d.arrow(divides_a_ty, with_product);
                d.arrow(coprime_ty, with_a)
            };

            let coprime_fv = d.fresh_fvar();
            let coprime = d.kernel().fvar(coprime_fv);
            let divides_a_fv = d.fresh_fvar();
            let divides_a = d.kernel().fvar(divides_a_fv);
            let divides_product_fv = d.fresh_fvar();
            let divides_product = d.kernel().fvar(divides_product_fv);
            let certificate = {
                let gcd_bezout = d.prelude().gcd_bezout;
                let base = d.lemma(gcd_bezout, &[a, c]);
                let motive = d.eq_motive(common, &|d, value| d.bezout(a, c, value));
                d.transport(common, motive, base, one, coprime)
            };
            let body = bezout_elim(
                d,
                a,
                c,
                one,
                conclusion,
                certificate,
                &|d, mp, mn, np, nn, equation| {
                    prove_cancellation_from_bezout(
                        d,
                        a,
                        c,
                        b,
                        divisor,
                        product,
                        divides_a,
                        divides_product,
                        mp,
                        mn,
                        np,
                        nn,
                        equation,
                    )
                },
            );
            let proof = d.lam_fv(divides_product_fv, divides_product_ty, body);
            let proof = d.lam_fv(divides_a_fv, divides_a_ty, proof);
            let proof = d.lam_fv(coprime_fv, coprime_ty, proof);
            (statement, proof)
        })
        .map_err(|error| {
            format!(
                "coprime-factor cancellation rejected: {}",
                d.explain(&error)
            )
        })?;
    }
    let declaration = kernel
        .environment()
        .get(target)
        .ok_or("coprime-factor cancellation disappeared")?;
    let Declaration::Theorem { ty, value, .. } = declaration else {
        return Err("coprime-factor cancellation is not a theorem".to_owned());
    };
    let ty = *ty;
    let value = *value;
    Ok(Admission {
        goal_sha256: canonical_expression_sha256(&kernel, ty)?,
        proof_sha256: canonical_expression_sha256(&kernel, value)?,
        declaration_sha256: canonical_declaration_sha256(&kernel, target)?,
        axiom_footprint: rendered_names(&kernel, &kernel.axiom_footprint(target)),
        direct_theorem_dependencies: rendered_names(&kernel, &kernel.theorem_dependencies(target)),
        kernel,
    })
}

#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]
fn prove_cancellation_from_bezout<D: NatOps>(
    d: &mut D,
    a: ExprId,
    c: ExprId,
    b: ExprId,
    divisor: ExprId,
    product: ExprId,
    divides_a: ExprId,
    divides_product: ExprId,
    mp: ExprId,
    mn: ExprId,
    np: ExprId,
    nn: ExprId,
    equation: ExprId,
) -> ExprId {
    let p = d.prelude();
    let one = d.num(1);
    let a_mn = d.mul(a, mn);
    let c_nn = d.mul(c, nn);
    let a_mp = d.mul(a, mp);
    let c_np = d.mul(c, np);
    let left_head = d.add(one, a_mn);
    let left = d.add(left_head, c_nn);
    let right = d.add(a_mp, c_np);

    let scaled = d.congr(left, right, equation, &|d, term| d.mul(term, b));
    let left_b = d.mul(left, b);
    let right_b = d.mul(right, b);
    let a_mn_b = d.mul(a_mn, b);
    let c_nn_b = d.mul(c_nn, b);
    let a_mp_b = d.mul(a_mp, b);
    let c_np_b = d.mul(c_np, b);

    let divides_a_multiple = |d: &mut D, factor: ExprId| {
        let a_factor = d.mul(a, factor);
        let first = d.lemma(p.dvd_mul_right_of_dvd, &[divisor, a, factor, divides_a]);
        d.lemma(p.dvd_mul_right_of_dvd, &[divisor, a_factor, b, first])
    };
    let divides_c_multiple = |d: &mut D, factor: ExprId| {
        let base = d.lemma(
            p.dvd_mul_right_of_dvd,
            &[divisor, product, factor, divides_product],
        );
        let product_factor = d.mul(product, factor);
        let c_factor = d.mul(c, factor);
        let flat = d.mul(c_factor, b);
        let b_factor = d.mul(b, factor);
        let factor_b = d.mul(factor, b);
        let step1 = d.lemma(p.mul_assoc, &[c, b, factor]);
        let nested_b_factor = d.mul(c, b_factor);
        let commute = d.lemma(p.mul_comm, &[b, factor]);
        let step2 = d.congr(b_factor, factor_b, commute, &|d, term| d.mul(c, term));
        let nested_factor_b = d.mul(c, factor_b);
        let assoc_back = d.lemma(p.mul_assoc, &[c, factor, b]);
        let step3 = d.symm(flat, nested_factor_b, assoc_back);
        let (_, chained) = d.chain(
            product_factor,
            &[
                (nested_b_factor, step1),
                (nested_factor_b, step2),
                (flat, step3),
            ],
        );
        let motive = d.eq_motive(product_factor, &|d, value| d.dvd(divisor, value));
        d.transport(product_factor, motive, base, flat, chained)
    };

    let d_a_mn_b = divides_a_multiple(d, mn);
    let d_c_nn_b = divides_c_multiple(d, nn);
    let d_a_mp_b = divides_a_multiple(d, mp);
    let d_c_np_b = divides_c_multiple(d, np);
    let excess = d.add(a_mn_b, c_nn_b);
    let divides_excess = d.lemma(p.dvd_add, &[divisor, a_mn_b, c_nn_b, d_a_mn_b, d_c_nn_b]);
    let total = d.add(a_mp_b, c_np_b);
    let divides_total = d.lemma(p.dvd_add, &[divisor, a_mp_b, c_np_b, d_a_mp_b, d_c_np_b]);
    let right_expand = d.lemma(p.right_distrib, &[a_mp, c_np, b]);
    let divides_right_b = {
        let back = d.symm(right_b, total, right_expand);
        let motive = d.eq_motive(total, &|d, value| d.dvd(divisor, value));
        d.transport(total, motive, divides_total, right_b, back)
    };

    let outer = d.lemma(p.right_distrib, &[left_head, c_nn, b]);
    let head_b = d.mul(left_head, b);
    let split_outer = d.add(head_b, c_nn_b);
    let inner_expand = d.lemma(p.right_distrib, &[one, a_mn, b]);
    let one_b = d.mul(one, b);
    let split_inner = d.add(one_b, a_mn_b);
    let step_inner = d.congr(head_b, split_inner, inner_expand, &|d, term| {
        d.add(term, c_nn_b)
    });
    let with_one = d.add(split_inner, c_nn_b);
    let one_mul = d.lemma(p.one_mul, &[b]);
    let b_plus = d.add(b, a_mn_b);
    let step_one = d.congr(one_b, b, one_mul, &|d, term| {
        let head = d.add(term, a_mn_b);
        d.add(head, c_nn_b)
    });
    let flattened = d.add(b_plus, c_nn_b);
    let assoc = d.lemma(p.add_assoc, &[b, a_mn_b, c_nn_b]);
    let b_plus_excess = d.add(b, excess);
    let (_, left_normalised) = d.chain(
        left_b,
        &[
            (split_outer, outer),
            (with_one, step_inner),
            (flattened, step_one),
            (b_plus_excess, assoc),
        ],
    );
    let back = d.symm(left_b, b_plus_excess, left_normalised);
    let (_, bridge) = d.chain(b_plus_excess, &[(left_b, back), (right_b, scaled)]);
    let divides_b_plus = {
        let back = d.symm(b_plus_excess, right_b, bridge);
        let motive = d.eq_motive(right_b, &|d, value| d.dvd(divisor, value));
        d.transport(right_b, motive, divides_right_b, b_plus_excess, back)
    };
    let excess_plus_b = d.add(excess, b);
    let commute = d.lemma(p.add_comm, &[b, excess]);
    let divides_excess_plus = {
        let motive = d.eq_motive(b_plus_excess, &|d, value| d.dvd(divisor, value));
        d.transport(
            b_plus_excess,
            motive,
            divides_b_plus,
            excess_plus_b,
            commute,
        )
    };
    let divides_b_ty = d.dvd(divisor, b);
    let divides_excess_plus_ty = d.dvd(divisor, excess_plus_b);
    let characterization = d.lemma(p.dvd_add_iff_right, &[divisor, excess, b, divides_excess]);
    let reverse = iff_reverse(d, divides_b_ty, divides_excess_plus_ty, characterization);
    d.apply(reverse, &[divides_excess_plus])
}

fn iff_reverse<D: NatOps>(d: &mut D, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let iff_ty = d.const_app(logic.iff, &[left, right]);
    let target = d.arrow(right, left);
    let motive = {
        let proof_fv = d.fresh_fvar();
        d.lam_fv(proof_fv, iff_ty, target)
    };
    let minor = {
        let forward_ty = d.arrow(left, right);
        let forward_fv = d.fresh_fvar();
        let reverse_fv = d.fresh_fvar();
        let reverse = d.kernel().fvar(reverse_fv);
        let with_reverse = d.lam_fv(reverse_fv, target, reverse);
        d.lam_fv(forward_fv, forward_ty, with_reverse)
    };
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.iff_rec, vec![zero]);
    d.apply(rec, &[left, right, motive, minor, proof])
}

#[allow(
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::type_complexity
)]
fn bezout_elim<D: NatOps>(
    d: &mut D,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    target: ExprId,
    certificate: ExprId,
    minor: &dyn Fn(&mut D, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_name = d.prelude().logic.exists_;
    let rec_name = d.prelude().logic.exists_rec;

    let mp_fv = d.fresh_fvar();
    let mp = d.kernel().fvar(mp_fv);
    let mn_fv = d.fresh_fvar();
    let mn = d.kernel().fvar(mn_fv);
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let nn_fv = d.fresh_fvar();
    let nn = d.kernel().fvar(nn_fv);
    let equation = d.bezout_equation(m, n, g, mp, mn, np, nn);
    let nn_predicate = d.lam_fv(nn_fv, nat, equation);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let nn_exists = d.apply(exists, &[nat, nn_predicate]);
    let np_predicate = d.lam_fv(np_fv, nat, nn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let np_exists = d.apply(exists, &[nat, np_predicate]);
    let mn_predicate = d.lam_fv(mn_fv, nat, np_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mn_exists = d.apply(exists, &[nat, mn_predicate]);
    let mp_predicate = d.lam_fv(mp_fv, nat, mn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mp_exists = d.apply(exists, &[nat, mp_predicate]);

    let equation_fv = d.fresh_fvar();
    let equation_proof = d.kernel().fvar(equation_fv);
    let core = minor(d, mp, mn, np, nn, equation_proof);
    let nn_minor = {
        let with_equation = d.lam_fv(equation_fv, equation, core);
        d.lam_fv(nn_fv, nat, with_equation)
    };
    let np_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, nn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, nn_predicate, motive, nn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, nn_exists, eliminated);
        d.lam_fv(np_fv, nat, with_witness)
    };
    let mn_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, np_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, np_predicate, motive, np_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, np_exists, eliminated);
        d.lam_fv(mn_fv, nat, with_witness)
    };
    let mp_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, mn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, mn_predicate, motive, mn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, mn_exists, eliminated);
        d.lam_fv(mp_fv, nat, with_witness)
    };
    let motive = d.kernel().lam(anon, mp_exists, target, BinderInfo::Default);
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[nat, mp_predicate, motive, mp_minor, certificate])
}

fn exact_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == rendered).then_some(name)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(format!("{rendered} occurs {} times", matches.len())),
    }
}

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    let mut name = kernel.anon();
    for part in parts {
        name = kernel.name_str(name, *part);
    }
    name
}

fn rendered_names(kernel: &Kernel, names: &[NameId]) -> Vec<String> {
    names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
}
