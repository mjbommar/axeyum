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

fn run() -> Result<(), String> {
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).map_err(|error| format!("{error:?}"))?;
    let root = kernel.anon();
    let axeyum = kernel.name_str(root, "Axeyum");
    let autogenesis = kernel.name_str(axeyum, "Autogenesis");
    let bit_to_bool_name = kernel.name_str(autogenesis, "bitToBool");
    let test_bit_bool_name = kernel.name_str(autogenesis, "testBitBool");
    let successor_name = kernel.name_str(autogenesis, "testBitBool_succ");

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
    println!(
        "NAT_TESTBIT_BOOL_BRIDGE_OK|theorem=Axeyum.Autogenesis.testBitBool_succ|axioms=0|type={}",
        kernel.render_lean(ty)
    );
    Ok(())
}
