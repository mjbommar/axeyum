//! Build the clean Boolean observation view over the native numeric `testBit`.
//!
//! This does not identify the view with imported Lean's `Nat.testBit`; that
//! later transport remains explicit. It proves the result-sort seam itself is
//! constructively bridgeable and preserves the native successor equation.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, NatDev, NatOps, NatPrelude, ReducibilityHint,
    build_nat_prelude,
};

fn iff_forward(d: &mut NatDev<'_>, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let iff_ty = d.const_app(logic.iff, &[left, right]);
    let target = d.arrow(left, right);
    let proof_fv = d.fresh_fvar();
    let motive = d.lam_fv(proof_fv, iff_ty, target);
    let forward_fv = d.fresh_fvar();
    let forward = d.kernel().fvar(forward_fv);
    let reverse_ty = d.arrow(right, left);
    let reverse_fv = d.fresh_fvar();
    let with_reverse = d.lam_fv(reverse_fv, reverse_ty, forward);
    let minor = d.lam_fv(forward_fv, target, with_reverse);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.iff_rec, vec![zero]);
    d.apply(rec, &[left, right, motive, minor, proof])
}

fn n_lt_mul_two(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, pos: ExprId) -> ExprId {
    let zero = d.zero();
    let add_n_zero = d.add(n, zero);
    let add_n_n = d.add(n, n);
    let step = d.lemma(p.add_lt_add_left, &[n, zero, n, pos]);
    let remove_zero = d.lemma(p.add_zero, &[n]);
    let motive = d.eq_motive(add_n_zero, &|d, value| d.lt(value, add_n_n));
    let n_lt_double = d.transport(add_n_zero, motive, step, n, remove_zero);
    let one = d.num(1);
    let two = d.succ(one);
    let product = d.mul(two, n);
    let one_product = d.mul(one, n);
    let expanded = d.add(one_product, n);
    let expand = d.lemma(p.succ_mul, &[one, n]);
    let one_mul = d.lemma(p.one_mul, &[n]);
    let simplify = d.congr(one_product, n, one_mul, &|d, value| d.add(value, n));
    let (_, product_eq_double) = d.chain(product, &[(expanded, expand), (add_n_n, simplify)]);
    let double_eq_product = d.symm(product, add_n_n, product_eq_double);
    let target_motive = d.eq_motive(add_n_n, &|d, value| d.lt(n, value));
    d.transport(
        add_n_n,
        target_motive,
        n_lt_double,
        product,
        double_eq_product,
    )
}

fn and_left(d: &mut NatDev<'_>, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let and_ty = d.const_app(logic.and, &[left, right]);
    let pair_fv = d.fresh_fvar();
    let motive = d.lam_fv(pair_fv, and_ty, left);
    let left_fv = d.fresh_fvar();
    let left_proof = d.kernel().fvar(left_fv);
    let right_fv = d.fresh_fvar();
    let with_right = d.lam_fv(right_fv, right, left_proof);
    let minor = d.lam_fv(left_fv, left, with_right);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.and_rec, vec![zero]);
    d.apply(rec, &[left, right, motive, minor, proof])
}

fn and_right(d: &mut NatDev<'_>, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let and_ty = d.const_app(logic.and, &[left, right]);
    let pair_fv = d.fresh_fvar();
    let motive = d.lam_fv(pair_fv, and_ty, right);
    let left_fv = d.fresh_fvar();
    let right_fv = d.fresh_fvar();
    let right_proof = d.kernel().fvar(right_fv);
    let with_right = d.lam_fv(right_fv, right, right_proof);
    let minor = d.lam_fv(left_fv, left, with_right);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.and_rec, vec![zero]);
    d.apply(rec, &[left, right, motive, minor, proof])
}

#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left: ExprId,
    right: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left, right]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(rec, &[left, right, motive, left_case, right_case, proof])
}

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-testbit-bool-bridge: {error}");
        std::process::exit(1);
    }
}

// The term construction mirrors the mathematical telescope; conventional
// one-letter variables keep the rendered theorem and its builder aligned.
#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]
fn run() -> Result<(), String> {
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).map_err(|error| format!("{error:?}"))?;
    let root = kernel.anon();
    let axeyum = kernel.name_str(root, "Axeyum");
    let autogenesis = kernel.name_str(axeyum, "Autogenesis");
    let bit_to_bool_name = kernel.name_str(autogenesis, "bitToBool");
    let test_bit_bool_name = kernel.name_str(autogenesis, "testBitBool");
    let successor_name = kernel.name_str(autogenesis, "testBitBool_succ");
    let zero_observation_name = kernel.name_str(autogenesis, "testBitBool_zero");
    let beyond_bound_name = kernel.name_str(autogenesis, "testBitBool_beyond_bound");
    let observation_name = kernel.name_str(autogenesis, "bitwiseObservation");
    let observation_apply_name = kernel.name_str(autogenesis, "bitwiseObservation_apply");
    let bool_to_bit_name = kernel.name_str(autogenesis, "boolToBit");
    let reify_bits_name = kernel.name_str(autogenesis, "reifyBits");
    let reify_bits_zero_name = kernel.name_str(autogenesis, "reifyBits_zero");
    let reify_bits_succ_name = kernel.name_str(autogenesis, "reifyBits_succ");
    let bool_to_bit_roundtrip_name = kernel.name_str(autogenesis, "boolToBit_roundtrip_zero");
    let bool_to_bit_le_one_name = kernel.name_str(autogenesis, "boolToBit_le_one");
    let bit_to_bool_roundtrip_name = kernel.name_str(autogenesis, "bitToBool_boolToBit");
    let bool_digit_div_mod_name = kernel.name_str(autogenesis, "boolDigit_divMod");
    let bool_digit_div_name = kernel.name_str(autogenesis, "boolDigit_div");
    let bool_digit_mod_name = kernel.name_str(autogenesis, "boolDigit_mod");
    let reify_low_name = kernel.name_str(autogenesis, "reifyBitsLow");
    let reify_low_zero_name = kernel.name_str(autogenesis, "reifyBitsLow_zero");
    let reify_low_succ_name = kernel.name_str(autogenesis, "reifyBitsLow_succ");
    let reify_low_roundtrip_name = kernel.name_str(autogenesis, "reifyBitsLow_roundtrip");
    let reify_low_outside_name = kernel.name_str(autogenesis, "reifyBitsLow_outside");
    let bitwise_reify_low_name = kernel.name_str(autogenesis, "bitwiseReifyLow");
    let bitwise_reify_low_roundtrip_name =
        kernel.name_str(autogenesis, "testBitBool_bitwiseReifyLow");
    let bitwise_total_name = kernel.name_str(autogenesis, "bitwiseTotal");
    let bitwise_total_theorem_name = kernel.name_str(autogenesis, "testBitBool_bitwiseTotal");
    let reify_one_normalize_name = kernel.name_str(autogenesis, "reifyBits_one_normalize");
    let reify_one_roundtrip_name = kernel.name_str(autogenesis, "reifyBits_one_roundtrip_zero");
    let reify_bound_name = kernel.name_str(autogenesis, "reifyBits_lt_pow");
    let numeric_roundtrip_name = kernel.name_str(autogenesis, "reifyBits_numeric_roundtrip");
    let bitwise_reify_name = kernel.name_str(autogenesis, "bitwiseReifyBounded");

    {
        let mut d = NatDev::new(&mut kernel, prelude);
        let nat = d.nat_ty();
        let bool_ty = d.bool_ty();
        let anon = d.anon_name();

        // bitToBool 0 = false; bitToBool (succ _) = true.
        let motive = d.kernel().lam(anon, nat, bool_ty, BinderInfo::Default);
        let false_value = d.bool_false();
        let step = {
            let n_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let true_value = d.bool_true();
            let with_ih = d.lam_fv(ih_fv, bool_ty, true_value);
            d.lam_fv(n_fv, nat, with_ih)
        };
        let one = d.level_one();
        let rec = d.kernel().const_(prelude.rec, vec![one]);
        let value = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = d.apply(rec, &[motive, false_value, step, n]);
            d.lam_fv(n_fv, nat, body)
        };
        let ty = d.arrow(nat, bool_ty);
        d.kernel()
            .add_declaration(Declaration::Definition {
                name: bit_to_bool_name,
                uparams: vec![],
                ty,
                value,
                hint: ReducibilityHint::Regular(2),
            })
            .map_err(|error| format!("bitToBool rejected: {error:?}"))?;

        // testBitBool n i := bitToBool (Nat.testBit n i).
        let value = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bit = d.const_app(prelude.test_bit, &[n, i]);
            let body = d.const_app(bit_to_bool_name, &[bit]);
            let with_i = d.lam_fv(i_fv, nat, body);
            d.lam_fv(n_fv, nat, with_i)
        };
        let nat_to_bool = d.arrow(nat, bool_ty);
        let ty = d.arrow(nat, nat_to_bool);
        d.kernel()
            .add_declaration(Declaration::Definition {
                name: test_bit_bool_name,
                uparams: vec![],
                ty,
                value,
                hint: ReducibilityHint::Regular(3),
            })
            .map_err(|error| format!("testBitBool rejected: {error:?}"))?;

        // The native numeric successor equation is definitional, so mapping
        // both sides through bitToBool is also closed by reflexivity.
        d.theorem(successor_name, 2, &|d, vars| {
            let (n, i) = (vars[0], vars[1]);
            let successor = d.succ(i);
            let lhs = d.const_app(test_bit_bool_name, &[n, successor]);
            let two = d.num(2);
            let half = d.div(n, two);
            let rhs = d.const_app(test_bit_bool_name, &[half, i]);
            (d.bool_eq(lhs, rhs), d.bool_refl(rhs))
        })
        .map_err(|error| format!("testBitBool_succ rejected: {error:?}"))?;

        // Every observation of zero is false. This is the terminal needed to
        // prove that a finite low-digit reification has no bits beyond its
        // declared width.
        let zero_motive = |d: &mut NatDev<'_>, index| {
            let zero = d.zero();
            let observed = d.const_app(test_bit_bool_name, &[zero, index]);
            let false_value = d.bool_false();
            d.bool_eq(observed, false_value)
        };
        let zero_base = |d: &mut NatDev<'_>| {
            let false_value = d.bool_false();
            d.bool_refl(false_value)
        };
        let zero_step = |d: &mut NatDev<'_>, index, ih| {
            let zero = d.zero();
            let successor = d.succ(index);
            let observed = d.const_app(test_bit_bool_name, &[zero, successor]);
            let observed_prior = d.const_app(test_bit_bool_name, &[zero, index]);
            let step = d.lemma(successor_name, &[zero, index]);
            let false_value = d.bool_false();
            d.bool_trans(observed, observed_prior, false_value, step, ih)
        };
        let index_fv = d.fresh_fvar();
        let index = d.kernel().fvar(index_fv);
        let proof = d.induct(&zero_motive, &zero_base, &zero_step, index);
        let statement = zero_motive(&mut d, index);
        let theorem_type = d.pi_fv(index_fv, nat, statement);
        let theorem_value = d.lam_fv(index_fv, nat, proof);
        d.declare_theorem(zero_observation_name, theorem_type, theorem_value)
            .map_err(|error| format!("testBitBool_zero rejected: {}", d.explain(&error)))?;

        // A deliberately simple sufficient-width theorem: if n <= bound,
        // then every bit at offset+bound is false. This is looser than
        // `Nat.size`, but its proof follows the executable divide-by-two
        // recursion directly and is enough to make bitwise total.
        let bound_motive = |d: &mut NatDev<'_>, bound| {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let within = d.le(n, bound);
            let offset_fv = d.fresh_fvar();
            let offset = d.kernel().fvar(offset_fv);
            let index = d.add(offset, bound);
            let observed = d.const_app(test_bit_bool_name, &[n, index]);
            let false_value = d.bool_false();
            let at_offset = d.bool_eq(observed, false_value);
            let all_offsets = d.pi_fv(offset_fv, nat, at_offset);
            let body = d.arrow(within, all_offsets);
            d.pi_fv(n_fv, nat, body)
        };
        let bound_base = |d: &mut NatDev<'_>| {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let zero = d.zero();
            let within = d.le(n, zero);
            let within_fv = d.fresh_fvar();
            let within_proof = d.kernel().fvar(within_fv);
            let offset_fv = d.fresh_fvar();
            let offset = d.kernel().fvar(offset_fv);
            let zero_le_n = d.lemma(prelude.zero_le, &[n]);
            let n_eq_zero = d.lemma(prelude.le_antisymm, &[n, zero, within_proof, zero_le_n]);
            let zero_eq_n = d.symm(n, zero, n_eq_zero);
            let zero_observation = d.lemma(zero_observation_name, &[offset]);
            let zero_source_motive = d.eq_motive(zero, &|d, value| {
                let observed = d.const_app(test_bit_bool_name, &[value, offset]);
                let false_value = d.bool_false();
                d.bool_eq(observed, false_value)
            });
            let result = d.transport(zero, zero_source_motive, zero_observation, n, zero_eq_n);
            let with_offset = d.lam_fv(offset_fv, nat, result);
            let with_bound = d.lam_fv(within_fv, within, with_offset);
            d.lam_fv(n_fv, nat, with_bound)
        };
        let bound_step = |d: &mut NatDev<'_>, bound, ih| {
            let successor_bound = d.succ(bound);
            let n_motive = |d: &mut NatDev<'_>, n| {
                let within = d.le(n, successor_bound);
                let offset_fv = d.fresh_fvar();
                let offset = d.kernel().fvar(offset_fv);
                let index = d.add(offset, successor_bound);
                let observed = d.const_app(test_bit_bool_name, &[n, index]);
                let false_value = d.bool_false();
                let at_offset = d.bool_eq(observed, false_value);
                let all_offsets = d.pi_fv(offset_fv, nat, at_offset);
                d.arrow(within, all_offsets)
            };
            let n_base = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let within = d.le(zero, successor_bound);
                let within_fv = d.fresh_fvar();
                let offset_fv = d.fresh_fvar();
                let offset = d.kernel().fvar(offset_fv);
                let index = d.add(offset, successor_bound);
                let proof = d.lemma(zero_observation_name, &[index]);
                let with_offset = d.lam_fv(offset_fv, nat, proof);
                d.lam_fv(within_fv, within, with_offset)
            };
            let n_step = |d: &mut NatDev<'_>, predecessor, _n_ih| {
                let n = d.succ(predecessor);
                let within = d.le(n, successor_bound);
                let within_fv = d.fresh_fvar();
                let within_proof = d.kernel().fvar(within_fv);
                let offset_fv = d.fresh_fvar();
                let offset = d.kernel().fvar(offset_fv);
                let prior_index = d.add(offset, bound);
                let index = d.add(offset, successor_bound);
                let two = d.num(2);
                let half = d.div(n, two);
                let one = d.num(1);
                let relation = d.lemma(prelude.div_mod_exec, &[one, n]);
                let remainder = d.modulo(n, two);
                let floor_iff_fn =
                    d.lemma(prelude.div_mod_lt_mul_iff, &[two, n, half, remainder, n]);
                let floor_iff = d.apply(floor_iff_fn, &[relation]);
                let twice_n = d.mul(two, n);
                let n_lt_twice_n_ty = d.lt(n, twice_n);
                let half_lt_n_ty = d.lt(half, n);
                let floor_forward = iff_forward(d, n_lt_twice_n_ty, half_lt_n_ty, floor_iff);
                let positive = d.zero_lt_succ(predecessor);
                let n_lt_twice_n = n_lt_mul_two(d, &prelude, n, positive);
                let half_lt_n = d.apply(floor_forward, &[n_lt_twice_n]);
                let half_lt_successor_bound = d.lemma(
                    prelude.lt_of_lt_of_le,
                    &[half, n, successor_bound, half_lt_n, within_proof],
                );
                let half_le_bound = d.lemma(
                    prelude.le_of_succ_le_succ,
                    &[half, bound, half_lt_successor_bound],
                );
                let tail_fn = d.apply(ih, &[half]);
                let tail_offsets = d.apply(tail_fn, &[half_le_bound]);
                let tail = d.apply(tail_offsets, &[offset]);
                let observed = d.const_app(test_bit_bool_name, &[n, index]);
                let observed_half = d.const_app(test_bit_bool_name, &[half, prior_index]);
                let step = d.lemma(successor_name, &[n, prior_index]);
                let false_value = d.bool_false();
                let result = d.bool_trans(observed, observed_half, false_value, step, tail);
                let with_offset = d.lam_fv(offset_fv, nat, result);
                d.lam_fv(within_fv, within, with_offset)
            };
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let proof = d.induct(&n_motive, &n_base, &n_step, n);
            d.lam_fv(n_fv, nat, proof)
        };
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let proof = d.induct(&bound_motive, &bound_base, &bound_step, bound);
        let statement = bound_motive(&mut d, bound);
        let theorem_type = d.pi_fv(bound_fv, nat, statement);
        let theorem_value = d.lam_fv(bound_fv, nat, proof);
        d.declare_theorem(beyond_bound_name, theorem_type, theorem_value)
            .map_err(|error| format!("testBitBool_beyond_bound rejected: {}", d.explain(&error)))?;

        // The pointwise Boolean algebra required by the target, separated from
        // the harder task of reifying all observations back into one Nat.
        let bool_binary = {
            let bool_to_bool = d.arrow(bool_ty, bool_ty);
            d.arrow(bool_ty, bool_to_bool)
        };
        let observation_value = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let left = d.const_app(test_bit_bool_name, &[x, i]);
            let right = d.const_app(test_bit_bool_name, &[y, i]);
            let body = d.apply(f, &[left, right]);
            let with_i = d.lam_fv(i_fv, nat, body);
            let with_y = d.lam_fv(y_fv, nat, with_i);
            let with_x = d.lam_fv(x_fv, nat, with_y);
            d.lam_fv(f_fv, bool_binary, with_x)
        };
        let observation_type = {
            let over_i = d.arrow(nat, bool_ty);
            let over_y = d.arrow(nat, over_i);
            let over_x = d.arrow(nat, over_y);
            d.arrow(bool_binary, over_x)
        };
        d.kernel()
            .add_declaration(Declaration::Definition {
                name: observation_name,
                uparams: vec![],
                ty: observation_type,
                value: observation_value,
                hint: ReducibilityHint::Regular(4),
            })
            .map_err(|error| format!("bitwiseObservation rejected: {error:?}"))?;

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lhs = d.const_app(observation_name, &[f, x, y, i]);
        let left = d.const_app(test_bit_bool_name, &[x, i]);
        let right = d.const_app(test_bit_bool_name, &[y, i]);
        let rhs = d.apply(f, &[left, right]);
        let statement = d.bool_eq(lhs, rhs);
        let proof = d.bool_refl(rhs);
        let mut theorem_type = statement;
        let mut theorem_value = proof;
        for (free, ty) in [(i_fv, nat), (y_fv, nat), (x_fv, nat), (f_fv, bool_binary)] {
            theorem_type = d.pi_fv(free, ty, theorem_type);
            theorem_value = d.lam_fv(free, ty, theorem_value);
        }
        d.declare_theorem(observation_apply_name, theorem_type, theorem_value)
            .map_err(|error| format!("bitwiseObservation_apply rejected: {error:?}"))?;

        // boolToBit false = 0; boolToBit true = 1.
        let bool_to_bit_value = {
            let motive = d.kernel().lam(anon, bool_ty, nat, BinderInfo::Default);
            let zero = d.zero();
            let one_value = d.num(1);
            let level = d.level_one();
            let rec = d.kernel().const_(prelude.logic.bool_rec, vec![level]);
            let bit_fv = d.fresh_fvar();
            let bit = d.kernel().fvar(bit_fv);
            let body = d.apply(rec, &[motive, zero, one_value, bit]);
            d.lam_fv(bit_fv, bool_ty, body)
        };
        let bool_to_bit_type = d.arrow(bool_ty, nat);
        d.kernel()
            .add_declaration(Declaration::Definition {
                name: bool_to_bit_name,
                uparams: vec![],
                ty: bool_to_bit_type,
                value: bool_to_bit_value,
                hint: ReducibilityHint::Regular(2),
            })
            .map_err(|error| format!("boolToBit rejected: {error:?}"))?;

        // reifyBits bits k := sumRange (fun i => boolToBit (bits i) * 2^i) k.
        let bits_type = d.arrow(nat, bool_ty);
        let reify_value = {
            let bits_fv = d.fresh_fvar();
            let bits = d.kernel().fvar(bits_fv);
            let count_fv = d.fresh_fvar();
            let count = d.kernel().fvar(count_fv);
            let index_fv = d.fresh_fvar();
            let index = d.kernel().fvar(index_fv);
            let observed = d.apply(bits, &[index]);
            let digit = d.const_app(bool_to_bit_name, &[observed]);
            let two = d.num(2);
            let place = d.pow(two, index);
            let term = d.mul(digit, place);
            let summand = d.lam_fv(index_fv, nat, term);
            let body = d.const_app(prelude.sum_range, &[summand, count]);
            let with_count = d.lam_fv(count_fv, nat, body);
            d.lam_fv(bits_fv, bits_type, with_count)
        };
        let reify_type = {
            let over_count = d.arrow(nat, nat);
            d.arrow(bits_type, over_count)
        };
        d.kernel()
            .add_declaration(Declaration::Definition {
                name: reify_bits_name,
                uparams: vec![],
                ty: reify_type,
                value: reify_value,
                hint: ReducibilityHint::Regular(5),
            })
            .map_err(|error| format!("reifyBits rejected: {error:?}"))?;

        let bits_fv = d.fresh_fvar();
        let bits = d.kernel().fvar(bits_fv);
        let zero = d.zero();
        let reified_zero = d.const_app(reify_bits_name, &[bits, zero]);
        let reify_zero_type = d.eq(reified_zero, zero);
        let reify_zero_proof = d.refl(zero);
        let theorem_type = d.pi_fv(bits_fv, bits_type, reify_zero_type);
        let theorem_value = d.lam_fv(bits_fv, bits_type, reify_zero_proof);
        d.declare_theorem(reify_bits_zero_name, theorem_type, theorem_value)
            .map_err(|error| format!("reifyBits_zero rejected: {error:?}"))?;

        let bits_fv = d.fresh_fvar();
        let bits = d.kernel().fvar(bits_fv);
        let count_fv = d.fresh_fvar();
        let count = d.kernel().fvar(count_fv);
        let successor = d.succ(count);
        let lhs = d.const_app(reify_bits_name, &[bits, successor]);
        let prefix = d.const_app(reify_bits_name, &[bits, count]);
        let observed = d.apply(bits, &[count]);
        let digit = d.const_app(bool_to_bit_name, &[observed]);
        let two = d.num(2);
        let place = d.pow(two, count);
        let term = d.mul(digit, place);
        let rhs = d.add(prefix, term);
        let statement = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let over_count_type = d.pi_fv(count_fv, nat, statement);
        let over_count_value = d.lam_fv(count_fv, nat, proof);
        let theorem_type = d.pi_fv(bits_fv, bits_type, over_count_type);
        let theorem_value = d.lam_fv(bits_fv, bits_type, over_count_value);
        d.declare_theorem(reify_bits_succ_name, theorem_type, theorem_value)
            .map_err(|error| format!("reifyBits_succ rejected: {error:?}"))?;

        // Mapping one Boolean to a numeric digit and observing bit zero returns
        // that Boolean. Connecting this to `reifyBits bits 1` additionally
        // needs weighted-sum normalization and is intentionally separate.
        let zero = d.zero();
        let selector_fv = d.fresh_fvar();
        let selector = d.kernel().fvar(selector_fv);
        let motive_body = {
            let digit = d.const_app(bool_to_bit_name, &[selector]);
            let observed = d.const_app(test_bit_bool_name, &[digit, zero]);
            d.bool_eq(observed, selector)
        };
        let motive = d.lam_fv(selector_fv, bool_ty, motive_body);
        let false_value = d.bool_false();
        let true_value = d.bool_true();
        let false_case = d.bool_refl(false_value);
        let true_case = d.bool_refl(true_value);
        let level_zero = d.kernel().level_zero();
        let rec = d.kernel().const_(prelude.logic.bool_rec, vec![level_zero]);
        let proof = d.apply(rec, &[motive, false_case, true_case, selector]);
        let theorem_type = d.pi_fv(selector_fv, bool_ty, motive_body);
        let theorem_value = d.lam_fv(selector_fv, bool_ty, proof);
        if let Err(error) =
            d.declare_theorem(bool_to_bit_roundtrip_name, theorem_type, theorem_value)
        {
            return Err(format!(
                "boolToBit_roundtrip_zero rejected: {}",
                d.explain(&error)
            ));
        }

        // Every Boolean digit maps into the numeric interval [0, 1].
        let selector_fv = d.fresh_fvar();
        let selector = d.kernel().fvar(selector_fv);
        let one_value = d.num(1);
        let motive_body = {
            let digit = d.const_app(bool_to_bit_name, &[selector]);
            d.le(digit, one_value)
        };
        let motive = d.lam_fv(selector_fv, bool_ty, motive_body);
        let false_case = d.lemma(prelude.zero_le, &[one_value]);
        let true_case = d.lemma(prelude.le_refl, &[one_value]);
        let level_zero = d.kernel().level_zero();
        let rec = d.kernel().const_(prelude.logic.bool_rec, vec![level_zero]);
        let proof = d.apply(rec, &[motive, false_case, true_case, selector]);
        let theorem_type = d.pi_fv(selector_fv, bool_ty, motive_body);
        let theorem_value = d.lam_fv(selector_fv, bool_ty, proof);
        d.declare_theorem(bool_to_bit_le_one_name, theorem_type, theorem_value)
            .map_err(|error| format!("boolToBit_le_one rejected: {error:?}"))?;

        // The direct conversion round trip, separate from reading the digit
        // through native `testBit` at index zero.
        let selector_fv = d.fresh_fvar();
        let selector = d.kernel().fvar(selector_fv);
        let motive_body = {
            let digit = d.const_app(bool_to_bit_name, &[selector]);
            let observed = d.const_app(bit_to_bool_name, &[digit]);
            d.bool_eq(observed, selector)
        };
        let motive = d.lam_fv(selector_fv, bool_ty, motive_body);
        let false_value = d.bool_false();
        let true_value = d.bool_true();
        let false_case = d.bool_refl(false_value);
        let true_case = d.bool_refl(true_value);
        let level_zero = d.kernel().level_zero();
        let rec = d.kernel().const_(prelude.logic.bool_rec, vec![level_zero]);
        let proof = d.apply(rec, &[motive, false_case, true_case, selector]);
        let theorem_type = d.pi_fv(selector_fv, bool_ty, motive_body);
        let theorem_value = d.lam_fv(selector_fv, bool_ty, proof);
        d.declare_theorem(bit_to_bool_roundtrip_name, theorem_type, theorem_value)
            .map_err(|error| format!("bitToBool_boolToBit rejected: {}", d.explain(&error)))?;

        // A Boolean low digit followed by an arbitrary binary tail is a
        // genuine Euclidean decomposition by two. This is the reusable
        // arithmetic decoder required by the recursive round-trip proof: the
        // quotient is the tail and the remainder is exactly the low digit.
        let selector_fv = d.fresh_fvar();
        let selector = d.kernel().fvar(selector_fv);
        let tail_fv = d.fresh_fvar();
        let tail = d.kernel().fvar(tail_fv);
        let digit = d.const_app(bool_to_bit_name, &[selector]);
        let two = d.num(2);
        let product = d.mul(two, tail);
        let encoded = d.add(digit, product);
        let reconstructed = d.add(product, digit);
        let equation_ty = d.eq(encoded, reconstructed);
        let equation = d.lemma(prelude.add_comm, &[digit, product]);
        let digit_le_one = d.lemma(bool_to_bit_le_one_name, &[selector]);
        let bound_ty = d.lt(digit, two);
        let one_value = d.num(1);
        let bound = d.lemma(prelude.lt_succ_of_le, &[digit, one_value, digit_le_one]);
        let relation_ty = d.div_mod(two, encoded, tail, digit);
        let relation = d.const_app(
            prelude.logic.and_intro,
            &[equation_ty, bound_ty, equation, bound],
        );
        let over_tail_type = d.pi_fv(tail_fv, nat, relation_ty);
        let over_tail_value = d.lam_fv(tail_fv, nat, relation);
        let theorem_type = d.pi_fv(selector_fv, bool_ty, over_tail_type);
        let theorem_value = d.lam_fv(selector_fv, bool_ty, over_tail_value);
        d.declare_theorem(bool_digit_div_mod_name, theorem_type, theorem_value)
            .map_err(|error| format!("boolDigit_divMod rejected: {}", d.explain(&error)))?;

        let executable = d.lemma(prelude.div_mod_exec, &[one_value, encoded]);
        let quotient = d.div(encoded, two);
        let remainder = d.modulo(encoded, two);
        let unique = d.lemma(
            prelude.div_mod_unique,
            &[
                two, encoded, tail, digit, quotient, remainder, relation, executable,
            ],
        );
        let quotient_forward_ty = d.eq(tail, quotient);
        let remainder_forward_ty = d.eq(digit, remainder);
        let quotient_forward = and_left(&mut d, quotient_forward_ty, remainder_forward_ty, unique);
        let remainder_forward =
            and_right(&mut d, quotient_forward_ty, remainder_forward_ty, unique);
        let quotient_statement = d.eq(quotient, tail);
        let quotient_proof = d.symm(tail, quotient, quotient_forward);
        let over_tail_type = d.pi_fv(tail_fv, nat, quotient_statement);
        let over_tail_value = d.lam_fv(tail_fv, nat, quotient_proof);
        let theorem_type = d.pi_fv(selector_fv, bool_ty, over_tail_type);
        let theorem_value = d.lam_fv(selector_fv, bool_ty, over_tail_value);
        d.declare_theorem(bool_digit_div_name, theorem_type, theorem_value)
            .map_err(|error| format!("boolDigit_div rejected: {}", d.explain(&error)))?;

        let remainder_statement = d.eq(remainder, digit);
        let remainder_proof = d.symm(digit, remainder, remainder_forward);
        let over_tail_type = d.pi_fv(tail_fv, nat, remainder_statement);
        let over_tail_value = d.lam_fv(tail_fv, nat, remainder_proof);
        let theorem_type = d.pi_fv(selector_fv, bool_ty, over_tail_type);
        let theorem_value = d.lam_fv(selector_fv, bool_ty, over_tail_value);
        d.declare_theorem(bool_digit_mod_name, theorem_type, theorem_value)
            .map_err(|error| format!("boolDigit_mod rejected: {}", d.explain(&error)))?;

        // A low-digit-first reifier whose recursion follows `testBit_succ`.
        // Unlike the weighted-sum presentation, each computational step
        // exposes exactly the quotient/remainder shape proved above.
        let bits_type = d.arrow(nat, bool_ty);
        let bits_to_nat = d.arrow(bits_type, nat);
        let reify_low_value = {
            let count_fv = d.fresh_fvar();
            let count = d.kernel().fvar(count_fv);
            let motive = d.kernel().lam(anon, nat, bits_to_nat, BinderInfo::Default);
            let base_bits_fv = d.fresh_fvar();
            let base_zero = d.zero();
            let base = d.lam_fv(base_bits_fv, bits_type, base_zero);
            let step = {
                let index_fv = d.fresh_fvar();
                let ih_fv = d.fresh_fvar();
                let ih = d.kernel().fvar(ih_fv);
                let bits_fv = d.fresh_fvar();
                let bits = d.kernel().fvar(bits_fv);
                let zero = d.zero();
                let low = d.apply(bits, &[zero]);
                let digit = d.const_app(bool_to_bit_name, &[low]);
                let tail_index_fv = d.fresh_fvar();
                let tail_index = d.kernel().fvar(tail_index_fv);
                let next = d.succ(tail_index);
                let tail_bit = d.apply(bits, &[next]);
                let shifted = d.lam_fv(tail_index_fv, nat, tail_bit);
                let tail = d.apply(ih, &[shifted]);
                let two = d.num(2);
                let doubled = d.mul(two, tail);
                let body = d.add(digit, doubled);
                let with_bits = d.lam_fv(bits_fv, bits_type, body);
                let with_ih = d.lam_fv(ih_fv, bits_to_nat, with_bits);
                d.lam_fv(index_fv, nat, with_ih)
            };
            for (label, expression) in [("motive", motive), ("base", base), ("step", step)] {
                d.kernel().infer(expression).map_err(|error| {
                    format!("reifyBitsLow {label} failed: {}", d.explain(&error))
                })?;
            }
            let level = d.level_one();
            let rec = d.kernel().const_(prelude.rec, vec![level]);
            let by_count = d.apply(rec, &[motive, base, step, count]);
            let bits_fv = d.fresh_fvar();
            let bits = d.kernel().fvar(bits_fv);
            let body = d.apply(by_count, &[bits]);
            let with_count = d.lam_fv(count_fv, nat, body);
            d.lam_fv(bits_fv, bits_type, with_count)
        };
        let nat_to_nat = d.arrow(nat, nat);
        let reify_low_type = d.arrow(bits_type, nat_to_nat);
        let inferred_reify_low_type = d
            .kernel()
            .infer(reify_low_value)
            .map_err(|error| format!("reifyBitsLow inference failed: {}", d.explain(&error)))?;
        if !d.kernel().def_eq(inferred_reify_low_type, reify_low_type) {
            return Err(format!(
                "reifyBitsLow inferred {} instead of {}",
                d.kernel().render_lean(inferred_reify_low_type),
                d.kernel().render_lean(reify_low_type)
            ));
        }
        d.kernel()
            .add_declaration(Declaration::Definition {
                name: reify_low_name,
                uparams: vec![],
                ty: reify_low_type,
                value: reify_low_value,
                hint: ReducibilityHint::Regular(5),
            })
            .map_err(|error| format!("reifyBitsLow rejected: {}", d.explain(&error)))?;

        let bits_fv = d.fresh_fvar();
        let bits = d.kernel().fvar(bits_fv);
        let zero = d.zero();
        let low_zero = d.const_app(reify_low_name, &[bits, zero]);
        let statement = d.eq(low_zero, zero);
        let proof = d.refl(zero);
        let theorem_type = d.pi_fv(bits_fv, bits_type, statement);
        let theorem_value = d.lam_fv(bits_fv, bits_type, proof);
        d.declare_theorem(reify_low_zero_name, theorem_type, theorem_value)
            .map_err(|error| format!("reifyBitsLow_zero rejected: {}", d.explain(&error)))?;

        let bits_fv = d.fresh_fvar();
        let bits = d.kernel().fvar(bits_fv);
        let count_fv = d.fresh_fvar();
        let count = d.kernel().fvar(count_fv);
        let successor = d.succ(count);
        let lhs = d.const_app(reify_low_name, &[bits, successor]);
        let zero = d.zero();
        let low = d.apply(bits, &[zero]);
        let digit = d.const_app(bool_to_bit_name, &[low]);
        let tail_index_fv = d.fresh_fvar();
        let tail_index = d.kernel().fvar(tail_index_fv);
        let next = d.succ(tail_index);
        let tail_bit = d.apply(bits, &[next]);
        let shifted = d.lam_fv(tail_index_fv, nat, tail_bit);
        let tail = d.const_app(reify_low_name, &[shifted, count]);
        let two = d.num(2);
        let doubled = d.mul(two, tail);
        let rhs = d.add(digit, doubled);
        let statement = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let over_count_type = d.pi_fv(count_fv, nat, statement);
        let over_count_value = d.lam_fv(count_fv, nat, proof);
        let theorem_type = d.pi_fv(bits_fv, bits_type, over_count_type);
        let theorem_value = d.lam_fv(bits_fv, bits_type, over_count_value);
        d.declare_theorem(reify_low_succ_name, theorem_type, theorem_value)
            .map_err(|error| format!("reifyBitsLow_succ rejected: {}", d.explain(&error)))?;

        // Every in-range observation of the low-digit-first reifier returns
        // the source Boolean. The outer induction consumes one encoded digit;
        // the inner index split follows testBit's zero/successor equations.
        let roundtrip_motive = |d: &mut NatDev<'_>, width| {
            let bits_fv = d.fresh_fvar();
            let bits = d.kernel().fvar(bits_fv);
            let index_fv = d.fresh_fvar();
            let index = d.kernel().fvar(index_fv);
            let in_range = d.lt(index, width);
            let encoded = d.const_app(reify_low_name, &[bits, width]);
            let observed = d.const_app(test_bit_bool_name, &[encoded, index]);
            let expected = d.apply(bits, &[index]);
            let equality = d.bool_eq(observed, expected);
            let body = d.arrow(in_range, equality);
            let over_index = d.pi_fv(index_fv, nat, body);
            d.pi_fv(bits_fv, bits_type, over_index)
        };
        let roundtrip_base = |d: &mut NatDev<'_>| {
            let bits_fv = d.fresh_fvar();
            let bits = d.kernel().fvar(bits_fv);
            let index_fv = d.fresh_fvar();
            let index = d.kernel().fvar(index_fv);
            let zero = d.zero();
            let in_range = d.lt(index, zero);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let encoded = d.const_app(reify_low_name, &[bits, zero]);
            let observed = d.const_app(test_bit_bool_name, &[encoded, index]);
            let expected = d.apply(bits, &[index]);
            let target = d.bool_eq(observed, expected);
            let impossible = d.lemma(prelude.not_lt_zero, &[index, hyp]);
            let false_ty = d.kernel().const_(prelude.logic.false_, vec![]);
            let anon = d.anon_name();
            let false_motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
            let level_zero = d.kernel().level_zero();
            let false_rec = d.kernel().const_(prelude.logic.false_rec, vec![level_zero]);
            let result = d.apply(false_rec, &[false_motive, impossible]);
            let with_hyp = d.lam_fv(hyp_fv, in_range, result);
            let with_index = d.lam_fv(index_fv, nat, with_hyp);
            d.lam_fv(bits_fv, bits_type, with_index)
        };
        let roundtrip_step = |d: &mut NatDev<'_>, width, ih| {
            let bits_fv = d.fresh_fvar();
            let bits = d.kernel().fvar(bits_fv);
            let index_fv = d.fresh_fvar();
            let index = d.kernel().fvar(index_fv);
            let successor_width = d.succ(width);
            let index_motive = |d: &mut NatDev<'_>, current_index| {
                let in_range = d.lt(current_index, successor_width);
                let encoded = d.const_app(reify_low_name, &[bits, successor_width]);
                let observed = d.const_app(test_bit_bool_name, &[encoded, current_index]);
                let expected = d.apply(bits, &[current_index]);
                let equality = d.bool_eq(observed, expected);
                d.arrow(in_range, equality)
            };
            let index_base = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let in_range = d.lt(zero, successor_width);
                let hyp_fv = d.fresh_fvar();
                let low = d.apply(bits, &[zero]);
                let encoded = d.const_app(reify_low_name, &[bits, successor_width]);
                let tail_index_fv = d.fresh_fvar();
                let tail_index = d.kernel().fvar(tail_index_fv);
                let next_tail_index = d.succ(tail_index);
                let shifted_bit = d.apply(bits, &[next_tail_index]);
                let shifted = d.lam_fv(tail_index_fv, nat, shifted_bit);
                let tail = d.const_app(reify_low_name, &[shifted, width]);
                let digit = d.const_app(bool_to_bit_name, &[low]);
                let two = d.num(2);
                let doubled = d.mul(two, tail);
                let expanded = d.add(digit, doubled);
                let encoded_expanded = d.lemma(reify_low_succ_name, &[bits, width]);
                let observed_encoded = d.const_app(test_bit_bool_name, &[encoded, zero]);
                let observed_expanded = d.const_app(test_bit_bool_name, &[expanded, zero]);
                let source_motive = d.eq_motive(encoded, &|d, value| {
                    let observation = d.const_app(test_bit_bool_name, &[value, zero]);
                    d.bool_eq(observed_encoded, observation)
                });
                let encoded_refl = d.bool_refl(observed_encoded);
                let encoded_transport = d.transport(
                    encoded,
                    source_motive,
                    encoded_refl,
                    expanded,
                    encoded_expanded,
                );
                let native_bit = d.const_app(prelude.test_bit, &[expanded, zero]);
                let remainder = d.modulo(expanded, two);
                let native_zero = d.lemma(prelude.test_bit_zero, &[expanded]);
                let native_motive = d.eq_motive(native_bit, &|d, value| {
                    let mapped = d.const_app(bit_to_bool_name, &[value]);
                    d.bool_eq(observed_expanded, mapped)
                });
                let expanded_refl = d.bool_refl(observed_expanded);
                let through_remainder = d.transport(
                    native_bit,
                    native_motive,
                    expanded_refl,
                    remainder,
                    native_zero,
                );
                let remainder_digit = d.lemma(bool_digit_mod_name, &[low, tail]);
                let mapped_remainder = d.const_app(bit_to_bool_name, &[remainder]);
                let mapped_digit = d.const_app(bit_to_bool_name, &[digit]);
                let remainder_motive = d.eq_motive(remainder, &|d, value| {
                    let mapped = d.const_app(bit_to_bool_name, &[value]);
                    d.bool_eq(mapped_remainder, mapped)
                });
                let remainder_refl = d.bool_refl(mapped_remainder);
                let through_digit = d.transport(
                    remainder,
                    remainder_motive,
                    remainder_refl,
                    digit,
                    remainder_digit,
                );
                let digit_roundtrip = d.lemma(bit_to_bool_roundtrip_name, &[low]);
                let first = d.bool_trans(
                    observed_encoded,
                    observed_expanded,
                    mapped_remainder,
                    encoded_transport,
                    through_remainder,
                );
                let second = d.bool_trans(
                    observed_encoded,
                    mapped_remainder,
                    mapped_digit,
                    first,
                    through_digit,
                );
                let result =
                    d.bool_trans(observed_encoded, mapped_digit, low, second, digit_roundtrip);
                d.lam_fv(hyp_fv, in_range, result)
            };
            let index_step = |d: &mut NatDev<'_>, prior_index, _index_ih| {
                let current_index = d.succ(prior_index);
                let in_range = d.lt(current_index, successor_width);
                let hyp_fv = d.fresh_fvar();
                let hyp = d.kernel().fvar(hyp_fv);
                let zero = d.zero();
                let low = d.apply(bits, &[zero]);
                let encoded = d.const_app(reify_low_name, &[bits, successor_width]);
                let tail_index_fv = d.fresh_fvar();
                let tail_index = d.kernel().fvar(tail_index_fv);
                let next_tail_index = d.succ(tail_index);
                let shifted_bit = d.apply(bits, &[next_tail_index]);
                let shifted = d.lam_fv(tail_index_fv, nat, shifted_bit);
                let tail = d.const_app(reify_low_name, &[shifted, width]);
                let digit = d.const_app(bool_to_bit_name, &[low]);
                let two = d.num(2);
                let doubled = d.mul(two, tail);
                let expanded = d.add(digit, doubled);
                let encoded_expanded = d.lemma(reify_low_succ_name, &[bits, width]);
                let quotient_encoded = d.div(encoded, two);
                let quotient_expanded = d.div(expanded, two);
                let quotient_congr = d.congr(encoded, expanded, encoded_expanded, &|d, value| {
                    d.div(value, two)
                });
                let quotient_tail = d.lemma(bool_digit_div_name, &[low, tail]);
                let quotient_eq = d.trans(
                    quotient_encoded,
                    quotient_expanded,
                    tail,
                    quotient_congr,
                    quotient_tail,
                );
                let observed_encoded = d.const_app(test_bit_bool_name, &[encoded, current_index]);
                let observed_quotient =
                    d.const_app(test_bit_bool_name, &[quotient_encoded, prior_index]);
                let successor_observation = d.lemma(successor_name, &[encoded, prior_index]);
                let observed_tail = d.const_app(test_bit_bool_name, &[tail, prior_index]);
                let quotient_motive = d.eq_motive(quotient_encoded, &|d, value| {
                    let observation = d.const_app(test_bit_bool_name, &[value, prior_index]);
                    d.bool_eq(observed_quotient, observation)
                });
                let quotient_refl = d.bool_refl(observed_quotient);
                let through_tail = d.transport(
                    quotient_encoded,
                    quotient_motive,
                    quotient_refl,
                    tail,
                    quotient_eq,
                );
                let successor_prior = d.succ(prior_index);
                let prior_in_range =
                    d.lemma(prelude.le_of_succ_le_succ, &[successor_prior, width, hyp]);
                let tail_roundtrip_fn = d.apply(ih, &[shifted, prior_index]);
                let tail_roundtrip = d.apply(tail_roundtrip_fn, &[prior_in_range]);
                let expected = d.apply(bits, &[current_index]);
                let first = d.bool_trans(
                    observed_encoded,
                    observed_quotient,
                    observed_tail,
                    successor_observation,
                    through_tail,
                );
                let result = d.bool_trans(
                    observed_encoded,
                    observed_tail,
                    expected,
                    first,
                    tail_roundtrip,
                );
                d.lam_fv(hyp_fv, in_range, result)
            };
            let proof_at_index = d.induct(&index_motive, &index_base, &index_step, index);
            let with_index = d.lam_fv(index_fv, nat, proof_at_index);
            d.lam_fv(bits_fv, bits_type, with_index)
        };
        let width_fv = d.fresh_fvar();
        let width = d.kernel().fvar(width_fv);
        let proof = d.induct(&roundtrip_motive, &roundtrip_base, &roundtrip_step, width);
        let statement = roundtrip_motive(&mut d, width);
        let theorem_type = d.pi_fv(width_fv, nat, statement);
        let theorem_value = d.lam_fv(width_fv, nat, proof);
        d.declare_theorem(reify_low_roundtrip_name, theorem_type, theorem_value)
            .map_err(|error| format!("reifyBitsLow_roundtrip rejected: {}", d.explain(&error)))?;

        // A width-k reification has no set bits at offset+k or beyond. The
        // index is stated as `offset + k` so the successor equation computes
        // in lockstep with the induction on k.
        let outside_motive = |d: &mut NatDev<'_>, width| {
            let bits_fv = d.fresh_fvar();
            let bits = d.kernel().fvar(bits_fv);
            let offset_fv = d.fresh_fvar();
            let offset = d.kernel().fvar(offset_fv);
            let index = d.add(offset, width);
            let encoded = d.const_app(reify_low_name, &[bits, width]);
            let observed = d.const_app(test_bit_bool_name, &[encoded, index]);
            let false_value = d.bool_false();
            let body = d.bool_eq(observed, false_value);
            let over_offset = d.pi_fv(offset_fv, nat, body);
            d.pi_fv(bits_fv, bits_type, over_offset)
        };
        let outside_base = |d: &mut NatDev<'_>| {
            let bits_fv = d.fresh_fvar();
            let offset_fv = d.fresh_fvar();
            let offset = d.kernel().fvar(offset_fv);
            let zero_case = d.lemma(zero_observation_name, &[offset]);
            let with_offset = d.lam_fv(offset_fv, nat, zero_case);
            d.lam_fv(bits_fv, bits_type, with_offset)
        };
        let outside_step = |d: &mut NatDev<'_>, width, ih| {
            let bits_fv = d.fresh_fvar();
            let bits = d.kernel().fvar(bits_fv);
            let offset_fv = d.fresh_fvar();
            let offset = d.kernel().fvar(offset_fv);
            let successor_width = d.succ(width);
            let index = d.add(offset, successor_width);
            let prior_index = d.add(offset, width);
            let encoded = d.const_app(reify_low_name, &[bits, successor_width]);
            let zero = d.zero();
            let low = d.apply(bits, &[zero]);
            let tail_index_fv = d.fresh_fvar();
            let tail_index = d.kernel().fvar(tail_index_fv);
            let next_tail_index = d.succ(tail_index);
            let shifted_bit = d.apply(bits, &[next_tail_index]);
            let shifted = d.lam_fv(tail_index_fv, nat, shifted_bit);
            let tail = d.const_app(reify_low_name, &[shifted, width]);
            let digit = d.const_app(bool_to_bit_name, &[low]);
            let two = d.num(2);
            let doubled = d.mul(two, tail);
            let expanded = d.add(digit, doubled);
            let encoded_expanded = d.lemma(reify_low_succ_name, &[bits, width]);
            let quotient_encoded = d.div(encoded, two);
            let quotient_expanded = d.div(expanded, two);
            let quotient_congr = d.congr(encoded, expanded, encoded_expanded, &|d, value| {
                d.div(value, two)
            });
            let quotient_tail = d.lemma(bool_digit_div_name, &[low, tail]);
            let quotient_eq = d.trans(
                quotient_encoded,
                quotient_expanded,
                tail,
                quotient_congr,
                quotient_tail,
            );
            let observed = d.const_app(test_bit_bool_name, &[encoded, index]);
            let observed_quotient =
                d.const_app(test_bit_bool_name, &[quotient_encoded, prior_index]);
            let observed_tail = d.const_app(test_bit_bool_name, &[tail, prior_index]);
            let successor_observation = d.lemma(successor_name, &[encoded, prior_index]);
            let quotient_motive = d.eq_motive(quotient_encoded, &|d, value| {
                let observation = d.const_app(test_bit_bool_name, &[value, prior_index]);
                d.bool_eq(observed_quotient, observation)
            });
            let quotient_refl = d.bool_refl(observed_quotient);
            let through_tail = d.transport(
                quotient_encoded,
                quotient_motive,
                quotient_refl,
                tail,
                quotient_eq,
            );
            let tail_outside = d.apply(ih, &[shifted, offset]);
            let false_value = d.bool_false();
            let first = d.bool_trans(
                observed,
                observed_quotient,
                observed_tail,
                successor_observation,
                through_tail,
            );
            let result = d.bool_trans(observed, observed_tail, false_value, first, tail_outside);
            let with_offset = d.lam_fv(offset_fv, nat, result);
            d.lam_fv(bits_fv, bits_type, with_offset)
        };
        let width_fv = d.fresh_fvar();
        let width = d.kernel().fvar(width_fv);
        let proof = d.induct(&outside_motive, &outside_base, &outside_step, width);
        let statement = outside_motive(&mut d, width);
        let theorem_type = d.pi_fv(width_fv, nat, statement);
        let theorem_value = d.lam_fv(width_fv, nat, proof);
        d.declare_theorem(reify_low_outside_name, theorem_type, theorem_value)
            .map_err(|error| format!("reifyBitsLow_outside rejected: {}", d.explain(&error)))?;

        // Specialize the general low-digit reifier to the target-owned
        // pointwise bitwise observation algebra.
        let bool_to_bool = d.arrow(bool_ty, bool_ty);
        let bool_binary = d.arrow(bool_ty, bool_to_bool);
        let bitwise_reify_low_value = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let width_fv = d.fresh_fvar();
            let width = d.kernel().fvar(width_fv);
            let index_fv = d.fresh_fvar();
            let index = d.kernel().fvar(index_fv);
            let observation = d.const_app(observation_name, &[f, x, y, index]);
            let bits = d.lam_fv(index_fv, nat, observation);
            let body = d.const_app(reify_low_name, &[bits, width]);
            let with_width = d.lam_fv(width_fv, nat, body);
            let with_y = d.lam_fv(y_fv, nat, with_width);
            let with_x = d.lam_fv(x_fv, nat, with_y);
            d.lam_fv(f_fv, bool_binary, with_x)
        };
        let over_width = d.arrow(nat, nat);
        let over_y = d.arrow(nat, over_width);
        let over_x = d.arrow(nat, over_y);
        let bitwise_reify_low_type = d.arrow(bool_binary, over_x);
        d.kernel()
            .add_declaration(Declaration::Definition {
                name: bitwise_reify_low_name,
                uparams: vec![],
                ty: bitwise_reify_low_type,
                value: bitwise_reify_low_value,
                hint: ReducibilityHint::Regular(7),
            })
            .map_err(|error| format!("bitwiseReifyLow rejected: {}", d.explain(&error)))?;

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let width_fv = d.fresh_fvar();
        let width = d.kernel().fvar(width_fv);
        let index_fv = d.fresh_fvar();
        let index = d.kernel().fvar(index_fv);
        let in_range = d.lt(index, width);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let encoded = d.const_app(bitwise_reify_low_name, &[f, x, y, width]);
        let observed = d.const_app(test_bit_bool_name, &[encoded, index]);
        let pointwise = d.const_app(observation_name, &[f, x, y, index]);
        let bits_index_fv = d.fresh_fvar();
        let bits_index = d.kernel().fvar(bits_index_fv);
        let bits_value = d.const_app(observation_name, &[f, x, y, bits_index]);
        let bits = d.lam_fv(bits_index_fv, nat, bits_value);
        let packed_roundtrip_fn = d.lemma(reify_low_roundtrip_name, &[width, bits, index]);
        let packed_roundtrip = d.apply(packed_roundtrip_fn, &[hyp]);
        let left = d.const_app(test_bit_bool_name, &[x, index]);
        let right = d.const_app(test_bit_bool_name, &[y, index]);
        let expected = d.apply(f, &[left, right]);
        let pointwise_apply = d.lemma(observation_apply_name, &[f, x, y, index]);
        let result = d.bool_trans(
            observed,
            pointwise,
            expected,
            packed_roundtrip,
            pointwise_apply,
        );
        let with_hyp = d.lam_fv(hyp_fv, in_range, result);
        let with_index = d.lam_fv(index_fv, nat, with_hyp);
        let with_width = d.lam_fv(width_fv, nat, with_index);
        let with_y = d.lam_fv(y_fv, nat, with_width);
        let with_x = d.lam_fv(x_fv, nat, with_y);
        let theorem_value = d.lam_fv(f_fv, bool_binary, with_x);
        let statement = d.bool_eq(observed, expected);
        let with_hyp_type = d.arrow(in_range, statement);
        let with_index_type = d.pi_fv(index_fv, nat, with_hyp_type);
        let with_width_type = d.pi_fv(width_fv, nat, with_index_type);
        let with_y_type = d.pi_fv(y_fv, nat, with_width_type);
        let with_x_type = d.pi_fv(x_fv, nat, with_y_type);
        let theorem_type = d.pi_fv(f_fv, bool_binary, with_x_type);
        d.declare_theorem(
            bitwise_reify_low_roundtrip_name,
            theorem_type,
            theorem_value,
        )
        .map_err(|error| {
            format!(
                "testBitBool_bitwiseReifyLow rejected: {}",
                d.explain(&error)
            )
        })?;

        // A total target-owned bitwise operation. The deliberately loose
        // width `x+y` avoids depending on a separate bit-size API; the
        // sufficient-width theorem above proves both inputs are false beyond
        // it. The usual `f false false = false` side condition then makes the
        // bounded construction extensionally correct at every index.
        let bitwise_total_value = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let width = d.add(x, y);
            let body = d.const_app(bitwise_reify_low_name, &[f, x, y, width]);
            let with_y = d.lam_fv(y_fv, nat, body);
            let with_x = d.lam_fv(x_fv, nat, with_y);
            d.lam_fv(f_fv, bool_binary, with_x)
        };
        let over_y = d.arrow(nat, nat);
        let over_x = d.arrow(nat, over_y);
        let bitwise_total_type = d.arrow(bool_binary, over_x);
        d.kernel()
            .add_declaration(Declaration::Definition {
                name: bitwise_total_name,
                uparams: vec![],
                ty: bitwise_total_type,
                value: bitwise_total_value,
                hint: ReducibilityHint::Regular(8),
            })
            .map_err(|error| format!("bitwiseTotal rejected: {}", d.explain(&error)))?;

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let false_value = d.bool_false();
        let false_false = d.apply(f, &[false_value, false_value]);
        let side_condition = d.bool_eq(false_false, false_value);
        let side_fv = d.fresh_fvar();
        let side = d.kernel().fvar(side_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let index_fv = d.fresh_fvar();
        let index = d.kernel().fvar(index_fv);
        let width = d.add(x, y);
        let total = d.const_app(bitwise_total_name, &[f, x, y]);
        let output = d.const_app(test_bit_bool_name, &[total, index]);
        let input_x = d.const_app(test_bit_bool_name, &[x, index]);
        let input_y = d.const_app(test_bit_bool_name, &[y, index]);
        let rhs = d.apply(f, &[input_x, input_y]);
        let goal = d.bool_eq(output, rhs);

        let x_le_width = d.lemma(prelude.le_add_right, &[x, y]);
        let y_plus_x = d.add(y, x);
        let y_le_yx = d.lemma(prelude.le_add_right, &[y, x]);
        let yx_eq_width = d.lemma(prelude.add_comm, &[y, x]);
        let y_bound_motive = d.eq_motive(y_plus_x, &|d, value| d.le(y, value));
        let y_le_width = d.transport(y_plus_x, y_bound_motive, y_le_yx, width, yx_eq_width);

        let bits_index_fv = d.fresh_fvar();
        let bits_index = d.kernel().fvar(bits_index_fv);
        let bit_value = d.const_app(observation_name, &[f, x, y, bits_index]);
        let output_bits = d.lam_fv(bits_index_fv, nat, bit_value);

        let outside_at = |d: &mut NatDev<'_>, offset, source_index, source_eq_index| {
            let output_source = d.const_app(test_bit_bool_name, &[total, source_index]);
            let output_false_source =
                d.lemma(reify_low_outside_name, &[width, output_bits, offset]);
            let output_index_motive = d.eq_motive(source_index, &|d, value| {
                let observed = d.const_app(test_bit_bool_name, &[total, value]);
                d.bool_eq(output_source, observed)
            });
            let output_source_refl = d.bool_refl(output_source);
            let output_index_transport = d.transport(
                source_index,
                output_index_motive,
                output_source_refl,
                index,
                source_eq_index,
            );
            let output_to_source = d.bool_symm(output_source, output, output_index_transport);
            let output_false = d.bool_trans(
                output,
                output_source,
                false_value,
                output_to_source,
                output_false_source,
            );

            let x_source = d.const_app(test_bit_bool_name, &[x, source_index]);
            let x_false_source = d.lemma(beyond_bound_name, &[width, x, x_le_width, offset]);
            let x_index_motive = d.eq_motive(source_index, &|d, value| {
                let observed = d.const_app(test_bit_bool_name, &[x, value]);
                d.bool_eq(x_source, observed)
            });
            let x_source_refl = d.bool_refl(x_source);
            let x_transport = d.transport(
                source_index,
                x_index_motive,
                x_source_refl,
                index,
                source_eq_index,
            );
            let x_to_source = d.bool_symm(x_source, input_x, x_transport);
            let x_false = d.bool_trans(input_x, x_source, false_value, x_to_source, x_false_source);

            let y_source = d.const_app(test_bit_bool_name, &[y, source_index]);
            let y_false_source = d.lemma(beyond_bound_name, &[width, y, y_le_width, offset]);
            let y_index_motive = d.eq_motive(source_index, &|d, value| {
                let observed = d.const_app(test_bit_bool_name, &[y, value]);
                d.bool_eq(y_source, observed)
            });
            let y_source_refl = d.bool_refl(y_source);
            let y_transport = d.transport(
                source_index,
                y_index_motive,
                y_source_refl,
                index,
                source_eq_index,
            );
            let y_to_source = d.bool_symm(y_source, input_y, y_transport);
            let y_false = d.bool_trans(input_y, y_source, false_value, y_to_source, y_false_source);

            let f_false_y = d.apply(f, &[false_value, input_y]);
            let x_motive = d.bool_eq_motive(input_x, &|d, value| {
                let replaced = d.apply(f, &[value, input_y]);
                d.bool_eq(rhs, replaced)
            });
            let rhs_refl = d.bool_refl(rhs);
            let replace_x = d.bool_transport(input_x, x_motive, rhs_refl, false_value, x_false);
            let y_motive = d.bool_eq_motive(input_y, &|d, value| {
                let replaced = d.apply(f, &[false_value, value]);
                d.bool_eq(f_false_y, replaced)
            });
            let f_false_y_refl = d.bool_refl(f_false_y);
            let replace_y =
                d.bool_transport(input_y, y_motive, f_false_y_refl, false_value, y_false);
            let rhs_to_false_false =
                d.bool_trans(rhs, f_false_y, false_false, replace_x, replace_y);
            let rhs_false = d.bool_trans(rhs, false_false, false_value, rhs_to_false_false, side);
            let false_rhs = d.bool_symm(rhs, false_value, rhs_false);
            d.bool_trans(output, false_value, rhs, output_false, false_rhs)
        };

        let i_le_width_ty = d.le(index, width);
        let width_le_i_ty = d.le(width, index);
        let i_le_width_fv = d.fresh_fvar();
        let i_le_width = d.kernel().fvar(i_le_width_fv);
        let strict_ty = d.lt(index, width);
        let equal_ty = d.eq(index, width);
        let strict_fv = d.fresh_fvar();
        let strict = d.kernel().fvar(strict_fv);
        let bounded_fn = d.lemma(bitwise_reify_low_roundtrip_name, &[f, x, y, width, index]);
        let bounded = d.apply(bounded_fn, &[strict]);
        let strict_case = d.lam_fv(strict_fv, strict_ty, bounded);
        let equal_fv = d.fresh_fvar();
        let equal = d.kernel().fvar(equal_fv);
        let width_eq_index = d.symm(index, width, equal);
        let zero = d.zero();
        let zero_plus_width = d.add(zero, width);
        let zero_plus_width_eq_width = d.lemma(prelude.zero_add, &[width]);
        let zero_plus_width_eq_index = d.trans(
            zero_plus_width,
            width,
            index,
            zero_plus_width_eq_width,
            width_eq_index,
        );
        let equal_case_proof = outside_at(&mut d, zero, zero_plus_width, zero_plus_width_eq_index);
        let equal_case = d.lam_fv(equal_fv, equal_ty, equal_case_proof);
        let strict_or_equal = d.lemma(prelude.lt_or_eq_of_le, &[index, width, i_le_width]);
        let inside_or_boundary = or_elim(
            &mut d,
            &prelude,
            strict_ty,
            equal_ty,
            goal,
            strict_case,
            equal_case,
            strict_or_equal,
        );
        let inside_case = d.lam_fv(i_le_width_fv, i_le_width_ty, inside_or_boundary);

        let width_le_i_fv = d.fresh_fvar();
        let width_le_i = d.kernel().fvar(width_le_i_fv);
        let offset = d.sub(index, width);
        let source_index = d.add(offset, width);
        let source_eq_index = d.lemma(prelude.sub_add_cancel, &[width, index, width_le_i]);
        let outside_proof = outside_at(&mut d, offset, source_index, source_eq_index);
        let outside_case = d.lam_fv(width_le_i_fv, width_le_i_ty, outside_proof);
        let totality = d.lemma(prelude.le_total, &[index, width]);
        let proof = or_elim(
            &mut d,
            &prelude,
            i_le_width_ty,
            width_le_i_ty,
            goal,
            inside_case,
            outside_case,
            totality,
        );
        let with_index = d.lam_fv(index_fv, nat, proof);
        let with_y = d.lam_fv(y_fv, nat, with_index);
        let with_x = d.lam_fv(x_fv, nat, with_y);
        let with_side = d.lam_fv(side_fv, side_condition, with_x);
        let theorem_value = d.lam_fv(f_fv, bool_binary, with_side);
        let with_index_type = d.pi_fv(index_fv, nat, goal);
        let with_y_type = d.pi_fv(y_fv, nat, with_index_type);
        let with_x_type = d.pi_fv(x_fv, nat, with_y_type);
        let with_side_type = d.pi_fv(side_fv, side_condition, with_x_type);
        let theorem_type = d.pi_fv(f_fv, bool_binary, with_side_type);
        d.declare_theorem(bitwise_total_theorem_name, theorem_type, theorem_value)
            .map_err(|error| format!("testBitBool_bitwiseTotal rejected: {}", d.explain(&error)))?;

        // The non-definitional arithmetic bridge from the one-element weighted
        // sum to its sole digit.
        let bits_fv = d.fresh_fvar();
        let bits = d.kernel().fvar(bits_fv);
        let zero = d.zero();
        let one_value = d.num(1);
        let selected = d.apply(bits, &[zero]);
        let digit = d.const_app(bool_to_bit_name, &[selected]);
        let reified = d.const_app(reify_bits_name, &[bits, one_value]);
        let prefix = d.const_app(reify_bits_name, &[bits, zero]);
        let two = d.num(2);
        let power = d.pow(two, zero);
        let weighted = d.mul(digit, power);
        let expanded = d.add(prefix, weighted);
        let step_eq = d.lemma(reify_bits_succ_name, &[bits, zero]);
        let prefix_zero = d.lemma(reify_bits_zero_name, &[bits]);
        let zero_weighted = d.add(zero, weighted);
        let replace_prefix = d.congr(prefix, zero, prefix_zero, &|d, value| {
            d.add(value, weighted)
        });
        let power_one = d.lemma(prelude.pow_zero, &[two]);
        let weighted_one = d.mul(digit, one_value);
        let zero_weighted_one = d.add(zero, weighted_one);
        let replace_power = d.congr(power, one_value, power_one, &|d, value| {
            let product = d.mul(digit, value);
            d.add(zero, product)
        });
        let remove_zero = d.lemma(prelude.zero_add, &[weighted_one]);
        let remove_one = d.lemma(prelude.mul_one, &[digit]);
        let (_, normalization) = d.chain(
            reified,
            &[
                (expanded, step_eq),
                (zero_weighted, replace_prefix),
                (zero_weighted_one, replace_power),
                (weighted_one, remove_zero),
                (digit, remove_one),
            ],
        );
        let normalization_type = d.eq(reified, digit);
        let theorem_type = d.pi_fv(bits_fv, bits_type, normalization_type);
        let theorem_value = d.lam_fv(bits_fv, bits_type, normalization);
        d.declare_theorem(reify_one_normalize_name, theorem_type, theorem_value)
            .map_err(|error| format!("reifyBits_one_normalize rejected: {error:?}"))?;

        // Transport the Boolean digit round trip across the checked arithmetic
        // normalization; this is the genuine one-bit weighted-sum round trip.
        let observed_reified = d.const_app(test_bit_bool_name, &[reified, zero]);
        let observed_digit = d.const_app(test_bit_bool_name, &[digit, zero]);
        let motive = d.eq_motive(reified, &|d, value| {
            let observed = d.const_app(test_bit_bool_name, &[value, zero]);
            d.bool_eq(observed_reified, observed)
        });
        let refl_case = d.bool_refl(observed_reified);
        let observed_transport = d.transport(reified, motive, refl_case, digit, normalization);
        let digit_roundtrip = d.lemma(bool_to_bit_roundtrip_name, &[selected]);
        let roundtrip = d.bool_trans(
            observed_reified,
            observed_digit,
            selected,
            observed_transport,
            digit_roundtrip,
        );
        let roundtrip_type = d.bool_eq(observed_reified, selected);
        let theorem_type = d.pi_fv(bits_fv, bits_type, roundtrip_type);
        let theorem_value = d.lam_fv(bits_fv, bits_type, roundtrip);
        d.declare_theorem(reify_one_roundtrip_name, theorem_type, theorem_value)
            .map_err(|error| format!("reifyBits_one_roundtrip_zero rejected: {error:?}"))?;

        // Every k-bit weighted sum is strictly below 2^k.
        let motive = |d: &mut NatDev<'_>, count| {
            let bits_fv = d.fresh_fvar();
            let bits = d.kernel().fvar(bits_fv);
            let reified = d.const_app(reify_bits_name, &[bits, count]);
            let two = d.num(2);
            let bound = d.pow(two, count);
            let body = d.lt(reified, bound);
            d.pi_fv(bits_fv, bits_type, body)
        };
        let base = |d: &mut NatDev<'_>| {
            let bits_fv = d.fresh_fvar();
            let zero = d.zero();
            let proof = d.lemma(prelude.zero_lt_succ, &[zero]);
            d.lam_fv(bits_fv, bits_type, proof)
        };
        let step = |d: &mut NatDev<'_>, count, ih| {
            let bits_fv = d.fresh_fvar();
            let bits = d.kernel().fvar(bits_fv);
            let one_value = d.num(1);
            let two = d.num(2);
            let power = d.pow(two, count);
            let prefix = d.const_app(reify_bits_name, &[bits, count]);
            let selected = d.apply(bits, &[count]);
            let digit = d.const_app(bool_to_bit_name, &[selected]);
            let weighted = d.mul(digit, power);
            let prefix_lt = d.apply(ih, &[bits]);
            let digit_le = d.lemma(bool_to_bit_le_one_name, &[selected]);

            let power_digit = d.mul(power, digit);
            let power_one = d.mul(power, one_value);
            let scaled = d.lemma(
                prelude.mul_le_mul_left,
                &[power, digit, one_value, digit_le],
            );
            let weighted_eq = d.lemma(prelude.mul_comm, &[digit, power]);
            let power_digit_eq_weighted = d.symm(weighted, power_digit, weighted_eq);
            let left_motive = d.eq_motive(power_digit, &|d, value| d.le(value, power_one));
            let weighted_le_power_one = d.transport(
                power_digit,
                left_motive,
                scaled,
                weighted,
                power_digit_eq_weighted,
            );
            let power_one_eq = d.lemma(prelude.mul_one, &[power]);
            let right_motive = d.eq_motive(power_one, &|d, value| d.le(weighted, value));
            let weighted_le_power = d.transport(
                power_one,
                right_motive,
                weighted_le_power_one,
                power,
                power_one_eq,
            );

            let weighted_prefix = d.add(weighted, prefix);
            let weighted_power = d.add(weighted, power);
            let lifted_lt = d.lemma(
                prelude.add_lt_add_left,
                &[weighted, prefix, power, prefix_lt],
            );
            let prefix_weighted = d.add(prefix, weighted);
            let power_weighted = d.add(power, weighted);
            let left_comm = d.lemma(prelude.add_comm, &[weighted, prefix]);
            let left_lt_motive =
                d.eq_motive(weighted_prefix, &|d, value| d.lt(value, weighted_power));
            let prefix_weighted_lt = d.transport(
                weighted_prefix,
                left_lt_motive,
                lifted_lt,
                prefix_weighted,
                left_comm,
            );
            let right_comm = d.lemma(prelude.add_comm, &[weighted, power]);
            let right_lt_motive =
                d.eq_motive(weighted_power, &|d, value| d.lt(prefix_weighted, value));
            let prefix_weighted_lt_power_weighted = d.transport(
                weighted_power,
                right_lt_motive,
                prefix_weighted_lt,
                power_weighted,
                right_comm,
            );
            let power_plus_power = d.add(power, power);
            let power_weighted_le_double = d.lemma(
                prelude.add_le_add_left,
                &[power, weighted, power, weighted_le_power],
            );
            let expanded_bound = d.lemma(
                prelude.lt_of_lt_of_le,
                &[
                    prefix_weighted,
                    power_weighted,
                    power_plus_power,
                    prefix_weighted_lt_power_weighted,
                    power_weighted_le_double,
                ],
            );

            let successor = d.succ(count);
            let reified_successor = d.const_app(reify_bits_name, &[bits, successor]);
            let step_eq = d.lemma(reify_bits_succ_name, &[bits, count]);
            let step_eq_rev = d.symm(reified_successor, prefix_weighted, step_eq);
            let source_motive =
                d.eq_motive(prefix_weighted, &|d, value| d.lt(value, power_plus_power));
            let reified_lt_double = d.transport(
                prefix_weighted,
                source_motive,
                expanded_bound,
                reified_successor,
                step_eq_rev,
            );

            let mul_power_two = d.mul(power, two);
            let mul_succ = d.lemma(prelude.mul_succ, &[power, one_value]);
            let mul_power_one = d.mul(power, one_value);
            let expanded_mul = d.add(mul_power_one, power);
            let mul_one = d.lemma(prelude.mul_one, &[power]);
            let simplify_mul = d.congr(mul_power_one, power, mul_one, &|d, value| {
                d.add(value, power)
            });
            let (_, mul_two_eq_double) = d.chain(
                mul_power_two,
                &[(expanded_mul, mul_succ), (power_plus_power, simplify_mul)],
            );
            let pow_successor = d.pow(two, successor);
            let pow_succ = d.lemma(prelude.pow_succ, &[two, count]);
            let (_, pow_eq_double) = d.chain(
                pow_successor,
                &[
                    (mul_power_two, pow_succ),
                    (power_plus_power, mul_two_eq_double),
                ],
            );
            let double_eq_pow = d.symm(pow_successor, power_plus_power, pow_eq_double);
            let target_motive =
                d.eq_motive(power_plus_power, &|d, value| d.lt(reified_successor, value));
            let result = d.transport(
                power_plus_power,
                target_motive,
                reified_lt_double,
                pow_successor,
                double_eq_pow,
            );
            d.lam_fv(bits_fv, bits_type, result)
        };
        let count_fv = d.fresh_fvar();
        let count = d.kernel().fvar(count_fv);
        let proof = d.induct(&motive, &base, &step, count);
        let motive_type = motive(&mut d, count);
        let theorem_type = d.pi_fv(count_fv, nat, motive_type);
        let theorem_value = d.lam_fv(count_fv, nat, proof);
        d.declare_theorem(reify_bound_name, theorem_type, theorem_value)
            .map_err(|error| format!("reifyBits_lt_pow rejected: {}", d.explain(&error)))?;

        // Reading the native numeric bits of a bounded reification and summing
        // them back reconstructs the exact same Nat.
        let count_fv = d.fresh_fvar();
        let count = d.kernel().fvar(count_fv);
        let bits_fv = d.fresh_fvar();
        let bits = d.kernel().fvar(bits_fv);
        let reified = d.const_app(reify_bits_name, &[bits, count]);
        let two = d.num(2);
        let power = d.pow(two, count);
        let index_fv = d.fresh_fvar();
        let index = d.kernel().fvar(index_fv);
        let native_bit = d.const_app(prelude.test_bit, &[reified, index]);
        let place = d.pow(two, index);
        let term = d.mul(native_bit, place);
        let summand = d.lam_fv(index_fv, nat, term);
        let reconstructed = d.const_app(prelude.sum_range, &[summand, count]);
        let remainder = d.modulo(reified, power);
        let partial = d.lemma(prelude.sum_test_bit_lt, &[count, reified]);
        let bound = d.lemma(reify_bound_name, &[count, bits]);
        let remove_mod = d.lemma(prelude.mod_eq_self_of_lt, &[reified, power, bound]);
        let proof = d.trans(reconstructed, remainder, reified, partial, remove_mod);
        let statement = d.eq(reconstructed, reified);
        let over_bits_type = d.pi_fv(bits_fv, bits_type, statement);
        let over_bits_value = d.lam_fv(bits_fv, bits_type, proof);
        let theorem_type = d.pi_fv(count_fv, nat, over_bits_type);
        let theorem_value = d.lam_fv(count_fv, nat, over_bits_value);
        d.declare_theorem(numeric_roundtrip_name, theorem_type, theorem_value)
            .map_err(|error| {
                format!(
                    "reifyBits_numeric_roundtrip rejected: {}",
                    d.explain(&error)
                )
            })?;

        // The bounded Nat candidate associated with the pointwise algebra.
        let reified_bitwise_value = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let count_fv = d.fresh_fvar();
            let count = d.kernel().fvar(count_fv);
            let index_fv = d.fresh_fvar();
            let index = d.kernel().fvar(index_fv);
            let observed = d.const_app(observation_name, &[f, x, y, index]);
            let bits = d.lam_fv(index_fv, nat, observed);
            let body = d.const_app(reify_bits_name, &[bits, count]);
            let with_count = d.lam_fv(count_fv, nat, body);
            let with_y = d.lam_fv(y_fv, nat, with_count);
            let with_x = d.lam_fv(x_fv, nat, with_y);
            d.lam_fv(f_fv, bool_binary, with_x)
        };
        let reified_bitwise_type = {
            let over_count = d.arrow(nat, nat);
            let over_y = d.arrow(nat, over_count);
            let over_x = d.arrow(nat, over_y);
            d.arrow(bool_binary, over_x)
        };
        d.kernel()
            .add_declaration(Declaration::Definition {
                name: bitwise_reify_name,
                uparams: vec![],
                ty: reified_bitwise_type,
                value: reified_bitwise_value,
                hint: ReducibilityHint::Regular(7),
            })
            .map_err(|error| format!("bitwiseReifyBounded rejected: {error:?}"))?;
    }

    let declaration = kernel
        .environment()
        .get(successor_name)
        .ok_or("testBitBool_succ disappeared")?;
    let ty = match declaration {
        Declaration::Theorem { ty, .. } => *ty,
        _ => return Err("testBitBool_succ is not a theorem".to_owned()),
    };
    let footprint: Vec<_> = kernel
        .axiom_footprint(successor_name)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    if !footprint.is_empty() {
        return Err(format!("bridge theorem has assumptions: {footprint:?}"));
    }
    let zero_observation_type = match kernel.environment().get(zero_observation_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("testBitBool_zero disappeared".to_owned()),
    };
    if !kernel.axiom_footprint(zero_observation_name).is_empty() {
        return Err("zero observation theorem gained assumptions".to_owned());
    }
    let beyond_bound_type = match kernel.environment().get(beyond_bound_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("testBitBool_beyond_bound disappeared".to_owned()),
    };
    if !kernel.axiom_footprint(beyond_bound_name).is_empty() {
        return Err("input sufficient-width theorem gained assumptions".to_owned());
    }
    let observation_type = match kernel.environment().get(observation_apply_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("bitwiseObservation_apply disappeared".to_owned()),
    };
    let observation_footprint = kernel.axiom_footprint(observation_apply_name);
    if !observation_footprint.is_empty() {
        return Err("bitwise observation algebra gained assumptions".to_owned());
    }
    let reify_zero_type = match kernel.environment().get(reify_bits_zero_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBits_zero disappeared".to_owned()),
    };
    if !kernel.axiom_footprint(reify_bits_zero_name).is_empty() {
        return Err("bounded reification base gained assumptions".to_owned());
    }
    let reify_succ_type = match kernel.environment().get(reify_bits_succ_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBits_succ disappeared".to_owned()),
    };
    if !kernel.axiom_footprint(reify_bits_succ_name).is_empty() {
        return Err("bounded reification step gained assumptions".to_owned());
    }
    let bool_to_bit_roundtrip_type = match kernel.environment().get(bool_to_bit_roundtrip_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("boolToBit_roundtrip_zero disappeared".to_owned()),
    };
    if !kernel
        .axiom_footprint(bool_to_bit_roundtrip_name)
        .is_empty()
    {
        return Err("Boolean digit roundtrip gained assumptions".to_owned());
    }
    let bool_to_bit_le_one_type = match kernel.environment().get(bool_to_bit_le_one_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("boolToBit_le_one disappeared".to_owned()),
    };
    if !kernel.axiom_footprint(bool_to_bit_le_one_name).is_empty() {
        return Err("Boolean digit bound gained assumptions".to_owned());
    }
    let bit_to_bool_roundtrip_type = match kernel.environment().get(bit_to_bool_roundtrip_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("bitToBool_boolToBit disappeared".to_owned()),
    };
    if !kernel
        .axiom_footprint(bit_to_bool_roundtrip_name)
        .is_empty()
    {
        return Err("direct Boolean digit roundtrip gained assumptions".to_owned());
    }
    let bool_digit_div_mod_type = match kernel.environment().get(bool_digit_div_mod_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("boolDigit_divMod disappeared".to_owned()),
    };
    let bool_digit_div_type = match kernel.environment().get(bool_digit_div_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("boolDigit_div disappeared".to_owned()),
    };
    let bool_digit_mod_type = match kernel.environment().get(bool_digit_mod_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("boolDigit_mod disappeared".to_owned()),
    };
    for name in [
        bool_digit_div_mod_name,
        bool_digit_div_name,
        bool_digit_mod_name,
    ] {
        if !kernel.axiom_footprint(name).is_empty() {
            return Err("Boolean low-digit decoder gained assumptions".to_owned());
        }
    }
    let reify_low_zero_type = match kernel.environment().get(reify_low_zero_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBitsLow_zero disappeared".to_owned()),
    };
    let reify_low_succ_type = match kernel.environment().get(reify_low_succ_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBitsLow_succ disappeared".to_owned()),
    };
    let reify_low_roundtrip_type = match kernel.environment().get(reify_low_roundtrip_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBitsLow_roundtrip disappeared".to_owned()),
    };
    let reify_low_outside_type = match kernel.environment().get(reify_low_outside_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBitsLow_outside disappeared".to_owned()),
    };
    for name in [
        reify_low_zero_name,
        reify_low_succ_name,
        reify_low_roundtrip_name,
        reify_low_outside_name,
    ] {
        if !kernel.axiom_footprint(name).is_empty() {
            return Err("low-digit-first reification gained assumptions".to_owned());
        }
    }
    let bitwise_reify_low_roundtrip_type =
        match kernel.environment().get(bitwise_reify_low_roundtrip_name) {
            Some(Declaration::Theorem { ty, .. }) => *ty,
            _ => return Err("testBitBool_bitwiseReifyLow disappeared".to_owned()),
        };
    if !kernel
        .axiom_footprint(bitwise_reify_low_roundtrip_name)
        .is_empty()
    {
        return Err("bounded bitwise theorem gained assumptions".to_owned());
    }
    let bitwise_total_theorem_type = match kernel.environment().get(bitwise_total_theorem_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("testBitBool_bitwiseTotal disappeared".to_owned()),
    };
    if !kernel
        .axiom_footprint(bitwise_total_theorem_name)
        .is_empty()
    {
        return Err("total bitwise theorem gained assumptions".to_owned());
    }
    let reify_one_normalize_type = match kernel.environment().get(reify_one_normalize_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBits_one_normalize disappeared".to_owned()),
    };
    let reify_one_roundtrip_type = match kernel.environment().get(reify_one_roundtrip_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBits_one_roundtrip_zero disappeared".to_owned()),
    };
    for name in [reify_one_normalize_name, reify_one_roundtrip_name] {
        if !kernel.axiom_footprint(name).is_empty() {
            return Err("one-bit weighted-sum evidence gained assumptions".to_owned());
        }
    }
    let reify_bound_type = match kernel.environment().get(reify_bound_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBits_lt_pow disappeared".to_owned()),
    };
    if !kernel.axiom_footprint(reify_bound_name).is_empty() {
        return Err("universal reification bound gained assumptions".to_owned());
    }
    let numeric_roundtrip_type = match kernel.environment().get(numeric_roundtrip_name) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err("reifyBits_numeric_roundtrip disappeared".to_owned()),
    };
    if !kernel.axiom_footprint(numeric_roundtrip_name).is_empty() {
        return Err("numeric reification roundtrip gained assumptions".to_owned());
    }
    println!(
        "NAT_TESTBIT_BOOL_BRIDGE_OK|theorem=Axeyum.Autogenesis.testBitBool_succ|axioms=0|type={}|zero_observation_theorem=Axeyum.Autogenesis.testBitBool_zero|zero_observation_axioms=0|zero_observation_type={}|input_bound_theorem=Axeyum.Autogenesis.testBitBool_beyond_bound|input_bound_axioms=0|input_bound_type={}|observation_theorem=Axeyum.Autogenesis.bitwiseObservation_apply|observation_axioms=0|observation_type={}|reification_definition=Axeyum.Autogenesis.bitwiseReifyBounded|reification_base_theorem=Axeyum.Autogenesis.reifyBits_zero|reification_base_axioms=0|reification_base_type={}|reification_step_theorem=Axeyum.Autogenesis.reifyBits_succ|reification_step_axioms=0|reification_step_type={}|boolean_digit_roundtrip_theorem=Axeyum.Autogenesis.boolToBit_roundtrip_zero|boolean_digit_roundtrip_axioms=0|boolean_digit_roundtrip_type={}|boolean_digit_bound_theorem=Axeyum.Autogenesis.boolToBit_le_one|boolean_digit_bound_axioms=0|boolean_digit_bound_type={}|direct_boolean_roundtrip_theorem=Axeyum.Autogenesis.bitToBool_boolToBit|direct_boolean_roundtrip_axioms=0|direct_boolean_roundtrip_type={}|boolean_digit_divmod_theorem=Axeyum.Autogenesis.boolDigit_divMod|boolean_digit_divmod_axioms=0|boolean_digit_divmod_type={}|boolean_digit_div_theorem=Axeyum.Autogenesis.boolDigit_div|boolean_digit_div_axioms=0|boolean_digit_div_type={}|boolean_digit_mod_theorem=Axeyum.Autogenesis.boolDigit_mod|boolean_digit_mod_axioms=0|boolean_digit_mod_type={}|low_reification_base_theorem=Axeyum.Autogenesis.reifyBitsLow_zero|low_reification_base_axioms=0|low_reification_base_type={}|low_reification_step_theorem=Axeyum.Autogenesis.reifyBitsLow_succ|low_reification_step_axioms=0|low_reification_step_type={}|low_reification_roundtrip_theorem=Axeyum.Autogenesis.reifyBitsLow_roundtrip|low_reification_roundtrip_axioms=0|low_reification_roundtrip_type={}|low_reification_outside_theorem=Axeyum.Autogenesis.reifyBitsLow_outside|low_reification_outside_axioms=0|low_reification_outside_type={}|bounded_bitwise_theorem=Axeyum.Autogenesis.testBitBool_bitwiseReifyLow|bounded_bitwise_axioms=0|bounded_bitwise_type={}|total_bitwise_theorem=Axeyum.Autogenesis.testBitBool_bitwiseTotal|total_bitwise_axioms=0|total_bitwise_type={}|one_bit_normalization_theorem=Axeyum.Autogenesis.reifyBits_one_normalize|one_bit_normalization_axioms=0|one_bit_normalization_type={}|one_bit_roundtrip_theorem=Axeyum.Autogenesis.reifyBits_one_roundtrip_zero|one_bit_roundtrip_axioms=0|one_bit_roundtrip_type={}|reification_bound_theorem=Axeyum.Autogenesis.reifyBits_lt_pow|reification_bound_axioms=0|reification_bound_type={}|numeric_roundtrip_theorem=Axeyum.Autogenesis.reifyBits_numeric_roundtrip|numeric_roundtrip_axioms=0|numeric_roundtrip_type={}",
        kernel.render_lean(ty),
        kernel.render_lean(zero_observation_type),
        kernel.render_lean(beyond_bound_type),
        kernel.render_lean(observation_type),
        kernel.render_lean(reify_zero_type),
        kernel.render_lean(reify_succ_type),
        kernel.render_lean(bool_to_bit_roundtrip_type),
        kernel.render_lean(bool_to_bit_le_one_type),
        kernel.render_lean(bit_to_bool_roundtrip_type),
        kernel.render_lean(bool_digit_div_mod_type),
        kernel.render_lean(bool_digit_div_type),
        kernel.render_lean(bool_digit_mod_type),
        kernel.render_lean(reify_low_zero_type),
        kernel.render_lean(reify_low_succ_type),
        kernel.render_lean(reify_low_roundtrip_type),
        kernel.render_lean(reify_low_outside_type),
        kernel.render_lean(bitwise_reify_low_roundtrip_type),
        kernel.render_lean(bitwise_total_theorem_type),
        kernel.render_lean(reify_one_normalize_type),
        kernel.render_lean(reify_one_roundtrip_type),
        kernel.render_lean(reify_bound_type),
        kernel.render_lean(numeric_roundtrip_type)
    );
    Ok(())
}
