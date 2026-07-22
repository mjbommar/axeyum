//! TL2.7 checked Nat literal typing and constructor-conversion gates.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, Kernel, KernelError, Lit, NatLit, ReducibilityHint,
    build_logic_prelude,
};

const BELOW_2_128: &str = "340282366920938463463374607431768211455";
const AT_2_128: &str = "340282366920938463463374607431768211456";

fn literal(digits: &str) -> Lit {
    Lit::Nat(NatLit::from_decimal(digits).expect("valid decimal natural"))
}

fn unary(
    kernel: &mut Kernel,
    zero: axeyum_lean_kernel::NameId,
    succ: axeyum_lean_kernel::NameId,
    n: usize,
) -> axeyum_lean_kernel::ExprId {
    let mut value = kernel.const_(zero, vec![]);
    for _ in 0..n {
        let constructor = kernel.const_(succ, vec![]);
        value = kernel.app(constructor, value);
    }
    value
}

#[test]
fn nat_literals_infer_only_against_the_checked_canonical_bootstrap() {
    let mut kernel = Kernel::new();
    let raw = kernel.lit(literal(AT_2_128));
    assert!(matches!(
        kernel.infer(raw),
        Err(KernelError::NatLiteralBootstrapMismatch { .. })
    ));

    let prelude = build_logic_prelude(&mut kernel);
    let nat = kernel.const_(prelude.nat, vec![]);
    assert_eq!(
        kernel.infer(raw).expect("canonical Nat enables literals"),
        nat
    );

    let string = kernel.lit(Lit::Str("still deferred".into()));
    assert!(matches!(
        kernel.infer(string),
        Err(KernelError::UnsupportedLit)
    ));
}

fn add_noncanonical_nat(kernel: &mut Kernel, shape: &str) {
    let anon = kernel.anon();
    let nat = kernel.name_str(anon, "Nat");
    let zero = kernel.name_str(nat, "zero");
    let succ = kernel.name_str(nat, "succ");
    let renamed = kernel.name_str(nat, "renamed");
    let nat_const = kernel.const_(nat, vec![]);
    let succ_type = kernel.pi(anon, nat_const, nat_const, BinderInfo::Default);
    let ty = if shape == "prop" {
        kernel.sort_zero()
    } else {
        let zero_level = kernel.level_zero();
        let one = kernel.level_succ(zero_level);
        kernel.sort(one)
    };
    let constructors = match shape {
        "missing-succ" => vec![(zero, nat_const)],
        "renamed" => vec![(zero, nat_const), (renamed, succ_type)],
        "reordered" => vec![(succ, succ_type), (zero, nat_const)],
        "prop" => vec![(zero, nat_const), (succ, succ_type)],
        _ => panic!("unknown noncanonical shape: {shape}"),
    };
    kernel
        .add_inductive(nat, &[], 0, ty, &constructors)
        .expect("the noncanonical control is independently well-formed");
}

#[test]
fn missing_renamed_reordered_and_wrong_sort_bootstraps_reject() {
    for shape in ["missing-succ", "renamed", "reordered", "prop"] {
        let mut kernel = Kernel::new();
        add_noncanonical_nat(&mut kernel, shape);
        let raw = kernel.lit(Lit::nat(1_u8));
        let error = kernel.infer(raw).unwrap_err();
        assert!(
            matches!(error, KernelError::NatLiteralBootstrapMismatch { .. }),
            "{shape}: {error:?}"
        );
    }
}

#[test]
fn literal_and_unary_constructor_forms_are_definitionally_equal() {
    let mut kernel = Kernel::new();
    let prelude = build_logic_prelude(&mut kernel);
    let zero = kernel.const_(prelude.nat_zero, vec![]);
    let literal_zero = kernel.lit(Lit::nat(0_u8));
    assert!(kernel.def_eq(literal_zero, zero));
    assert!(kernel.def_eq(zero, literal_zero));

    let unary_37 = unary(&mut kernel, prelude.nat_zero, prelude.nat_succ, 37);
    let literal_37 = kernel.lit(Lit::nat(37_u8));
    assert!(kernel.def_eq(literal_37, unary_37));
    assert!(kernel.def_eq(unary_37, literal_37));

    let below = kernel.lit(literal(BELOW_2_128));
    let at = kernel.lit(literal(AT_2_128));
    let succ = kernel.const_(prelude.nat_succ, vec![]);
    let boundary_constructor = kernel.app(succ, below);
    assert!(kernel.def_eq(at, boundary_constructor));
    assert!(kernel.def_eq(boundary_constructor, at));

    let literal_38 = kernel.lit(Lit::nat(38_u8));
    assert!(!kernel.def_eq(literal_37, literal_38));
    let succ_37 = kernel.app(succ, literal_37);
    assert!(!kernel.def_eq(literal_37, succ_37));
    let unary_one = unary(&mut kernel, prelude.nat_zero, prelude.nat_succ, 1);
    assert!(!kernel.def_eq(literal_zero, unary_one));
}

#[test]
fn delta_wrappers_reach_offset_equality_without_changing_literal_values() {
    let mut kernel = Kernel::new();
    let prelude = build_logic_prelude(&mut kernel);
    let anon = kernel.anon();
    let nat = kernel.const_(prelude.nat, vec![]);
    let value = kernel.lit(Lit::nat(7_u8));
    let alias = kernel.name_str(anon, "sevenAlias");
    kernel
        .add_declaration(Declaration::Definition {
            name: alias,
            uparams: vec![],
            ty: nat,
            value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("literal-backed definition admits");
    let alias = kernel.const_(alias, vec![]);
    let unary = unary(&mut kernel, prelude.nat_zero, prelude.nat_succ, 7);
    assert!(kernel.def_eq(alias, unary));
    assert!(kernel.def_eq(unary, alias));
}

#[test]
fn successor_and_recursor_convert_literals_but_general_nat_ops_stay_inert() {
    let mut kernel = Kernel::new();
    let prelude = build_logic_prelude(&mut kernel);
    let anon = kernel.anon();
    let level_zero = kernel.level_zero();
    let level_one = kernel.level_succ(level_zero);
    let nat = kernel.const_(prelude.nat, vec![]);
    let succ = kernel.const_(prelude.nat_succ, vec![]);

    let below = kernel.lit(literal(BELOW_2_128));
    let succ_below = kernel.app(succ, below);
    let at = kernel.lit(literal(AT_2_128));
    assert_eq!(kernel.whnf(succ_below), at);

    let motive = kernel.lam(anon, nat, nat, BinderInfo::Default);
    let step = {
        let ih = kernel.bvar(0);
        let succ_ih = kernel.app(succ, ih);
        let inner = kernel.lam(anon, nat, succ_ih, BinderInfo::Default);
        kernel.lam(anon, nat, inner, BinderInfo::Default)
    };
    let recursor = kernel.const_(prelude.nat_rec, vec![level_one]);
    let literal_zero = kernel.lit(Lit::nat(0_u8));
    let literal_three = kernel.lit(Lit::nat(3_u8));
    let rec = kernel.app(recursor, motive);
    let rec = kernel.app(rec, literal_zero);
    let rec = kernel.app(rec, step);
    let rec = kernel.app(rec, literal_three);
    assert_eq!(kernel.whnf(rec), literal_three);

    let add = kernel.name_str(prelude.nat, "add");
    let add_type = {
        let result = kernel.pi(anon, nat, nat, BinderInfo::Default);
        kernel.pi(anon, nat, result, BinderInfo::Default)
    };
    kernel
        .add_declaration(Declaration::Axiom {
            name: add,
            uparams: vec![],
            ty: add_type,
        })
        .expect("unaccelerated Nat.add control admits");
    let add = kernel.const_(add, vec![]);
    let add = kernel.app(add, literal_three);
    let add = kernel.app(add, literal_three);
    assert_eq!(kernel.whnf(add), add, "TL2.8 Nat.add must remain inert");
}
