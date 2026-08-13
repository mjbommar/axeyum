//! Regression coverage for the composable-prelude contract (ADR-0387).

use axeyum_lean_kernel::{
    Declaration, ExprId, Kernel, LogicPrelude, build_arith_prelude, build_int_prelude,
    build_logic_prelude, build_nat_prelude, build_string_prelude,
};

fn apply2(kernel: &mut Kernel, function: ExprId, lhs: ExprId, rhs: ExprId) -> ExprId {
    let applied = kernel.app(function, lhs);
    kernel.app(applied, rhs)
}

fn reflexivity(
    kernel: &mut Kernel,
    logic: LogicPrelude,
    level: axeyum_lean_kernel::LevelId,
    carrier: ExprId,
    value: ExprId,
) -> (ExprId, ExprId) {
    let equality = kernel.const_(logic.eq, vec![level]);
    let proposition = {
        let applied = kernel.app(equality, carrier);
        apply2(kernel, applied, value, value)
    };
    let refl = kernel.const_(logic.eq_refl, vec![level]);
    let proof = apply2(kernel, refl, carrier, value);
    (proposition, proof)
}

#[test]
fn all_preludes_compose_repeat_exactly_and_check_a_mixed_nat_int_proof() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let nat = build_nat_prelude(&mut kernel).expect("Nat prelude must compose");
    let int = build_int_prelude(&mut kernel).expect("Int prelude must compose");
    let real = build_arith_prelude(&mut kernel).expect("Real prelude must compose");
    let string2 = build_string_prelude(&mut kernel, logic, 2).expect("string prelude must compose");
    let string3 = build_string_prelude(&mut kernel, logic, 3)
        .expect("a distinct string alphabet must compose");

    assert_eq!(kernel.display_name(nat.add).to_string(), "Nat.add");
    assert_eq!(kernel.display_name(int.z).to_string(), "Int");
    assert_eq!(kernel.display_name(int.add).to_string(), "Int.add");
    assert_eq!(kernel.display_name(real.r).to_string(), "Real");
    assert_eq!(kernel.display_name(real.add).to_string(), "Real.add");
    assert_ne!(string2.char_ind, string3.char_ind);

    let nat_type = kernel.const_(nat.logic.nat, vec![]);
    let nat_zero = kernel.const_(nat.logic.nat_zero, vec![]);
    let nat_add = kernel.const_(nat.add, vec![]);
    let nat_sum = apply2(&mut kernel, nat_add, nat_zero, nat_zero);
    let inferred_nat = kernel
        .infer(nat_sum)
        .expect("Nat.add application must infer");
    assert!(kernel.def_eq(inferred_nat, nat_type));

    let int_type = kernel.const_(int.z, vec![]);
    let int_zero = kernel.const_(int.zero, vec![]);
    let int_add = kernel.const_(int.add, vec![]);
    let int_sum = apply2(&mut kernel, int_add, int_zero, int_zero);
    let inferred_int = kernel
        .infer(int_sum)
        .expect("Int.add application must infer");
    assert!(kernel.def_eq(inferred_int, int_type));

    let real_type = kernel.const_(real.r, vec![]);
    let real_zero = kernel.const_(real.zero, vec![]);
    let real_add = kernel.const_(real.add, vec![]);
    let real_sum = apply2(&mut kernel, real_add, real_zero, real_zero);
    let inferred_real = kernel
        .infer(real_sum)
        .expect("Real.add application must infer");
    assert!(kernel.def_eq(inferred_real, real_type));

    let level_one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let (nat_eq, nat_refl) = reflexivity(&mut kernel, logic, level_one, nat_type, nat_zero);
    let (int_eq, int_refl) = reflexivity(&mut kernel, logic, level_one, int_type, int_zero);
    let conjunction = {
        let and = kernel.const_(logic.and, vec![]);
        apply2(&mut kernel, and, nat_eq, int_eq)
    };
    let mixed_proof = {
        let intro = kernel.const_(logic.and_intro, vec![]);
        let applied = apply2(&mut kernel, intro, nat_eq, int_eq);
        apply2(&mut kernel, applied, nat_refl, int_refl)
    };
    let inferred_mixed = kernel
        .infer(mixed_proof)
        .expect("the mixed Nat/Int proof must check");
    assert!(kernel.def_eq(inferred_mixed, conjunction));

    let environment_len = kernel.environment().len();
    assert_eq!(
        build_logic_prelude(&mut kernel).expect("logic repeat must validate"),
        logic
    );
    assert_eq!(
        build_nat_prelude(&mut kernel).expect("Nat repeat must validate"),
        nat
    );
    assert_eq!(
        build_int_prelude(&mut kernel).expect("Int repeat must validate"),
        int
    );
    assert_eq!(
        build_arith_prelude(&mut kernel).expect("Real repeat must validate"),
        real
    );
    assert_eq!(
        build_string_prelude(&mut kernel, logic, 2).expect("string repeat must validate"),
        string2
    );
    assert_eq!(kernel.environment().len(), environment_len);
}

#[test]
fn late_reserved_name_conflict_rolls_back_the_entire_attempt() {
    let mut kernel = Kernel::new();
    build_logic_prelude(&mut kernel).expect("logic prelude must build");

    // `Int.eq_em` is the final member admitted by the integer builder. A wrong
    // pre-existing declaration therefore exercises rollback after the rest of
    // the package has passed the trusted gate.
    let anon = kernel.anon();
    let int_name = kernel.name_str(anon, "Int");
    let conflict_name = kernel.name_str(int_name, "eq_em");
    let prop = kernel.sort_zero();
    kernel
        .add_declaration(Declaration::Axiom {
            name: conflict_name,
            uparams: vec![],
            ty: prop,
        })
        .expect("the deliberate conflict must itself be well formed");

    let before: Vec<Declaration> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| declaration.clone())
        .collect();
    assert!(build_int_prelude(&mut kernel).is_err());
    let after: Vec<Declaration> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| declaration.clone())
        .collect();
    assert_eq!(after, before, "a failed package build must be atomic");
    assert!(kernel.environment().contains(conflict_name));
    assert!(kernel.environment().get(int_name).is_none());
}
