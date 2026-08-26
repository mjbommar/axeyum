//! Build the clean Boolean observation view over the native numeric `testBit`.
//!
//! This does not identify the view with imported Lean's `Nat.testBit`; that
//! later transport remains explicit. It proves the result-sort seam itself is
//! constructively bridgeable and preserves the native successor equation.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, Kernel, NatDev, NatOps, ReducibilityHint, build_nat_prelude,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-testbit-bool-bridge: {error}");
        std::process::exit(1);
    }
}

// The term construction mirrors the mathematical telescope; conventional
// one-letter variables keep the rendered theorem and its builder aligned.
#[allow(clippy::many_single_char_names, clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).map_err(|error| format!("{error:?}"))?;
    let root = kernel.anon();
    let axeyum = kernel.name_str(root, "Axeyum");
    let autogenesis = kernel.name_str(axeyum, "Autogenesis");
    let bit_to_bool_name = kernel.name_str(autogenesis, "bitToBool");
    let test_bit_bool_name = kernel.name_str(autogenesis, "testBitBool");
    let successor_name = kernel.name_str(autogenesis, "testBitBool_succ");
    let observation_name = kernel.name_str(autogenesis, "bitwiseObservation");
    let observation_apply_name = kernel.name_str(autogenesis, "bitwiseObservation_apply");
    let bool_to_bit_name = kernel.name_str(autogenesis, "boolToBit");
    let reify_bits_name = kernel.name_str(autogenesis, "reifyBits");
    let reify_bits_zero_name = kernel.name_str(autogenesis, "reifyBits_zero");
    let reify_bits_succ_name = kernel.name_str(autogenesis, "reifyBits_succ");
    let bool_to_bit_roundtrip_name = kernel.name_str(autogenesis, "boolToBit_roundtrip_zero");
    let bool_to_bit_le_one_name = kernel.name_str(autogenesis, "boolToBit_le_one");
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
        "NAT_TESTBIT_BOOL_BRIDGE_OK|theorem=Axeyum.Autogenesis.testBitBool_succ|axioms=0|type={}|observation_theorem=Axeyum.Autogenesis.bitwiseObservation_apply|observation_axioms=0|observation_type={}|reification_definition=Axeyum.Autogenesis.bitwiseReifyBounded|reification_base_theorem=Axeyum.Autogenesis.reifyBits_zero|reification_base_axioms=0|reification_base_type={}|reification_step_theorem=Axeyum.Autogenesis.reifyBits_succ|reification_step_axioms=0|reification_step_type={}|boolean_digit_roundtrip_theorem=Axeyum.Autogenesis.boolToBit_roundtrip_zero|boolean_digit_roundtrip_axioms=0|boolean_digit_roundtrip_type={}|boolean_digit_bound_theorem=Axeyum.Autogenesis.boolToBit_le_one|boolean_digit_bound_axioms=0|boolean_digit_bound_type={}|one_bit_normalization_theorem=Axeyum.Autogenesis.reifyBits_one_normalize|one_bit_normalization_axioms=0|one_bit_normalization_type={}|one_bit_roundtrip_theorem=Axeyum.Autogenesis.reifyBits_one_roundtrip_zero|one_bit_roundtrip_axioms=0|one_bit_roundtrip_type={}|reification_bound_theorem=Axeyum.Autogenesis.reifyBits_lt_pow|reification_bound_axioms=0|reification_bound_type={}|numeric_roundtrip_theorem=Axeyum.Autogenesis.reifyBits_numeric_roundtrip|numeric_roundtrip_axioms=0|numeric_roundtrip_type={}",
        kernel.render_lean(ty),
        kernel.render_lean(observation_type),
        kernel.render_lean(reify_zero_type),
        kernel.render_lean(reify_succ_type),
        kernel.render_lean(bool_to_bit_roundtrip_type),
        kernel.render_lean(bool_to_bit_le_one_type),
        kernel.render_lean(reify_one_normalize_type),
        kernel.render_lean(reify_one_roundtrip_type),
        kernel.render_lean(reify_bound_type),
        kernel.render_lean(numeric_roundtrip_type)
    );
    Ok(())
}
