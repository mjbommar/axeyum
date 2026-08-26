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
    println!(
        "NAT_TESTBIT_BOOL_BRIDGE_OK|theorem=Axeyum.Autogenesis.testBitBool_succ|axioms=0|type={}|observation_theorem=Axeyum.Autogenesis.bitwiseObservation_apply|observation_axioms=0|observation_type={}|reification_definition=Axeyum.Autogenesis.bitwiseReifyBounded|reification_base_theorem=Axeyum.Autogenesis.reifyBits_zero|reification_base_axioms=0|reification_base_type={}|reification_step_theorem=Axeyum.Autogenesis.reifyBits_succ|reification_step_axioms=0|reification_step_type={}",
        kernel.render_lean(ty),
        kernel.render_lean(observation_type),
        kernel.render_lean(reify_zero_type),
        kernel.render_lean(reify_succ_type)
    );
    Ok(())
}
