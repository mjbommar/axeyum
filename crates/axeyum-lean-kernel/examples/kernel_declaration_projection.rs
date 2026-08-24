//! Emit the complete constructed-prelude declaration surface for Autogenesis.
//!
//! Rows are `prelude<TAB>kind<TAB>name<TAB>axiom-footprint-size<TAB>` followed
//! by a comma-separated list of *direct theorem dependencies*.  The last field
//! is deliberately empty for non-theorems: a definition/recursor dependency
//! closure is not proof-term theorem dependency and must not be conflated with
//! it by the knowledge overlay.

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_complex_prelude, build_cpoint_prelude,
    build_creal_prelude, build_int_prelude, build_logic_prelude, build_nat_prelude,
    build_rat_prelude, build_string_prelude,
};

fn kind(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom { .. } => "axiom",
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
        Declaration::Quotient { .. } => "quotient",
    }
}

fn emit(label: &str, kernel: &Kernel) {
    let mut rows = kernel
        .environment()
        .iter()
        .map(|(name, declaration)| {
            let rendered = kernel.display_name(*name).to_string();
            let direct_theorems = if matches!(declaration, Declaration::Theorem { .. }) {
                kernel
                    .theorem_dependencies(*name)
                    .into_iter()
                    .map(|dependency| kernel.display_name(dependency).to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            } else {
                String::new()
            };
            let footprint_size = kernel.axiom_footprint(*name).len();
            (rendered, kind(declaration), footprint_size, direct_theorems)
        })
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| left.0.cmp(&right.0));
    for (name, declaration_kind, footprint_size, dependencies) in rows {
        println!("{label}\t{declaration_kind}\t{name}\t{footprint_size}\t{dependencies}");
    }
}

fn main() {
    let mut logic = Kernel::new();
    let _ = build_logic_prelude(&mut logic).expect("logic prelude must build");
    emit("logic", &logic);

    let mut nat = Kernel::new();
    let _ = build_nat_prelude(&mut nat).expect("Nat prelude must build");
    emit("nat", &nat);

    let mut axreal = Kernel::new();
    let _ = build_arith_prelude(&mut axreal).expect("AxReal prelude must build");
    emit("axreal", &axreal);

    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    emit("integer", &integer);

    let mut rational = Kernel::new();
    let _ = build_rat_prelude(&mut rational).expect("Rat prelude must build");
    emit("rat", &rational);

    let mut string = Kernel::new();
    let logic_handle = build_logic_prelude(&mut string).expect("logic prelude must build");
    let _ = build_string_prelude(&mut string, logic_handle, 2).expect("String prelude must build");
    emit("string", &string);

    let mut creal = Kernel::new();
    let _ = build_creal_prelude(&mut creal).expect("CReal prelude must build");
    emit("creal", &creal);

    let mut complex = Kernel::new();
    let _ = build_complex_prelude(&mut complex).expect("Complex prelude must build");
    emit("complex", &complex);

    let mut cpoint = Kernel::new();
    let _ = build_cpoint_prelude(&mut cpoint).expect("CPoint prelude must build");
    emit("cpoint", &cpoint);
}
