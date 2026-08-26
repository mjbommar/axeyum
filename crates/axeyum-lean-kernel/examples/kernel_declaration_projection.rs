//! Emit the complete constructed-prelude declaration surface for Autogenesis.
//!
//! Rows carry both all-kind direct declaration references and the theorem-only
//! subset. The latter remains the proof dependency relation; the former is
//! search vocabulary and must not be confused with a transitive closure.

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_characterization, build_complex_prelude,
    build_cpoint_prelude, build_creal_prelude, build_int_prelude, build_logic_prelude,
    build_nat_prelude, build_rat_prelude, build_string_prelude,
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
            let direct_declarations = kernel
                .declaration_dependencies(*name)
                .into_iter()
                .map(|dependency| kernel.display_name(dependency).to_string())
                .collect::<Vec<_>>()
                .join(",");
            let canonical_type = kernel.render_lean(declaration.ty());
            assert!(
                !canonical_type.contains(['\t', '\n', '\r']),
                "canonical declaration type must remain one TSV field"
            );
            let footprint_size = kernel.axiom_footprint(*name).len();
            (
                rendered,
                kind(declaration),
                footprint_size,
                direct_declarations,
                direct_theorems,
                canonical_type,
            )
        })
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| left.0.cmp(&right.0));
    for (
        name,
        declaration_kind,
        footprint_size,
        direct_declarations,
        direct_theorems,
        canonical_type,
    ) in rows
    {
        println!(
            "{label}\t{declaration_kind}\t{name}\t{footprint_size}\t{direct_declarations}\t{direct_theorems}\t{canonical_type}"
        );
    }
}

fn main() {
    // RUN THE WHOLE PROJECTION ON A DEEP STACK, not the process's main thread.
    //
    // This example builds every constructed prelude, and `Kernel::add_declaration`
    // recurses deeply enough through them to overflow the default 8 MiB
    // main-thread stack: `gen-autogenesis-kernel-dependency-projection.py`
    // shells out to it and got `died with <Signals.SIGABRT: 6>`, so the
    // projection could not be regenerated at all and had gone stale -- a lane
    // measured it holding 195 `Rat.*` declarations and zero `det2`, `cramer`
    // or `fib`.
    //
    // Same fix, and the same reasoning, as `theorem_dependency_inventory`:
    // `--release` happens to survive, but a doc note saying so cannot reach a
    // caller that does not read it. `complex`/`cpoint`'s own test modules use
    // `stack_size(64 * 1024 * 1024)`; do it here and every caller works
    // unchanged, debug or release.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(run)
        .expect("spawn the deep-stack worker")
        .join()
        .expect("the deep-stack worker must not panic");
}

fn run() {
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

    let mut characterization = Kernel::new();
    let _ =
        build_characterization(&mut characterization).expect("Nat/Int characterization must build");
    emit("characterization", &characterization);

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
